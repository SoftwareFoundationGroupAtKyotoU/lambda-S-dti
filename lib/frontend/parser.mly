%{
open Syntax
open Syntax.ITGL
open Utils.Error
open Type_utils

let tyvenv = ref Environment.empty

(* for function definition *)
let param_to_fun r (x, u) e = match u with
  | None -> FunExp (r, (x.value, Impl, fresh_tyvar ()), e)
  | Some u -> FunExp (r, (x.value, Expl, u), e)

(* for recursive function definition *)
let param_to_fun_ty r (x, u1) (e, u) = match u1 with
  | None ->
    let u1 = fresh_tyvar () in
    FunExp (r, (x.value, Impl, u1), e), TyFun (u1, u)
  | Some u1 ->
    FunExp (r, (x.value, Expl, u1), e), TyFun (u1, u)

let opt_ty_to_fresh_ty = function
  | None -> fresh_tyvar ()
  | Some u -> u

let make_seq r e1 e2 = LetExp (r, "_", AscExp (range_of_exp e1, e1, TyUnit), e2)

let dummy_var x = Var (dummy_range, x, ref [])

let make_for r i e1 e2 tag e3 = 
  let e1 = fun k -> LetExp (dummy_range, "_for_l", AscExp (range_of_exp e1, e1, TyInt), k) in
  let e2 = fun k -> LetExp (dummy_range, "_for_r", AscExp (range_of_exp e2, e2, TyInt), k) in
  let cond_op, loop_op = match tag with
    | `To ->     Lte, Plus
    | `Downto -> Gte, Minus
  in
  let loop_cond = BinOp (dummy_range, cond_op, dummy_var i, dummy_var "_for_r") in
  let loop_then = make_seq r e3 (AppExp (r, dummy_var "_for_loop", BinOp (dummy_range, loop_op, dummy_var i, IConst (dummy_range, 1)))) in
  let loop_content = IfExp (r, loop_cond, loop_then, UConst r) in
  let loop = fun k -> LetExp (r, "_for_loop", FixExp (r, "_for_loop", (i, Expl, TyInt), TyUnit, loop_content), k) in
  e1 @@ e2 @@ loop (AppExp (r, dummy_var "_for_loop", dummy_var "_for_l"))

let make_while r e1 e2 = 
  let loop_then = make_seq r e2 (AppExp (r, dummy_var "_while_loop", UConst dummy_range)) in
  let loop_content = IfExp (r, e1, loop_then, UConst r) in
  LetExp (r, "_while_loop", FixExp (r, "_while_loop", ("_", Expl, TyUnit), TyUnit, loop_content), AppExp (r, dummy_var "_while_loop", UConst dummy_range))

exception Parser_bug of string

%}

%token <Utils.Error.range> LPAREN RPAREN SEMI SEMISEMI COLON EQ QUOTE
%token <Utils.Error.range> PLUS MINUS STAR DIV MOD LT LTE GT GTE NEQ LAND LOR
%token <Utils.Error.range> LET REC IN FUN IF THEN ELSE FUNCTION
%token <Utils.Error.range> INT BOOL UNIT QUESTION RARROW
%token <Utils.Error.range> TRUE FALSE
%token <Utils.Error.range> COLCOL LBRACKET RBRACKET LIST
%token <Utils.Error.range> MATCH WITH VBAR UNDER
%token <Utils.Error.range> COMMA
%token <Utils.Error.range> REF SUBSTITUTE BANG
%token <Utils.Error.range> ARRAY MAKEARRAY LENGTHARRAY DOT LARROW
%token <Utils.Error.range> FOR TO DOWNTO DO DONE WHILE

%token <int Utils.Error.with_range> INTV
%token <Syntax.id Utils.Error.with_range> ID

%start toplevel
%type <Syntax.ITGL.program> toplevel

(* Ref: https://caml.inria.fr/pub/docs/manual-ocaml/expr.html *)
%nonassoc prec_match
%nonassoc below_semi
%right    SEMI
%right    SUBSTITUTE LARROW
%right    RARROW
%right    LOR
%right    LAND
%left     EQ NEQ LT LTE GT GTE VBAR
%right    COLCOL
%left     PLUS MINUS
%left     STAR DIV MOD

%%

toplevel :
  | p=Program {
      tyvenv := Environment.empty;
      p
    }

Program :
  | Expr SEMISEMI { Exp $1 }
  | start=LET x=ID params=list(Param) u=OptTypeAnnot EQ e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let e = match u with None -> e | Some u -> AscExp (range_of_exp e, e, u) in
      let e = List.fold_right (param_to_fun r) params e in
      LetDecl (x.value, e)
    }
  | start=LET REC x=ID params=nonempty_list(Param) u2=OptTypeAnnot EQ e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let u2 = opt_ty_to_fresh_ty u2 in
      match params with
      | [] ->
        raise @@ Parser_bug "params must not be empty"
      | (y, None) :: params ->
        let u1 = fresh_tyvar () in
        let e, u2 = List.fold_right (param_to_fun_ty r) params (e, u2) in
        LetDecl (x.value, FixExp (r, x.value, (y.value, Impl, u1), u2, e))
      | (y, Some u1) :: params ->
        let e, u2 = List.fold_right (param_to_fun_ty r) params (e, u2) in
        LetDecl (x.value, FixExp (r, x.value, (y.value, Expl, u1), u2, e))
    }

Expr :
  | e1=BelowSemiExpr SEMI e2=Expr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      make_seq r e1 e2
    }
  | NoSemiExpr { $1 }

NoSemiExpr :
  | LetExpr       { $1 }
  | FunExpr       { $1 }
  | MatchExpr     { $1 }
  | BelowSemiExpr { $1 } %prec below_semi

Param :
  | x=ID { (x, None) }
  | start=LPAREN last=RPAREN { ({ value = "_"; range = join_range start last }, Some TyUnit ) }
  | LPAREN x=ID COLON u=Type RPAREN { (x, Some u) }

%inline OptTypeAnnot :
  | /* empty */ { None }
  | COLON u=Type { Some u }

%inline OptSimpleTypeAnnot :
  | /* empty */ { None }
  | COLON u=SimpleType { Some u }

LetExpr :
  | start=LET x=ID params=list(Param) u1=OptTypeAnnot EQ e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let e1 = match u1 with None -> e1 | Some u1 -> AscExp (range_of_exp e1, e1, u1) in
      let e1 = List.fold_right (param_to_fun r) params e1 in
      LetExp (r, x.value, e1, e2)
    }
  | start=LET REC x=ID params=nonempty_list(Param) u2=OptTypeAnnot EQ e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let u2 = opt_ty_to_fresh_ty u2 in
      match params with
      | [] ->
        raise @@ Parser_bug "params must not be empty"
      | (y, None) :: params ->
        let u1 = fresh_tyvar () in
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixExp (r, x.value, (y.value, Impl, u1), u2, e1), e2)
      | (y, Some u1) :: params ->
        let e1, u2 = List.fold_right (param_to_fun_ty r) params (e1, u2) in
        LetExp (r, x.value, FixExp (r, x.value, (y.value, Expl, u1), u2, e1), e2)
    }

FunExpr :
  | start=FUN params=nonempty_list(Param) u=OptSimpleTypeAnnot RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      let e = match u with None -> e | Some u -> AscExp (range_of_exp e, e, u) in
      List.fold_right (param_to_fun r) params e
    }
  | start=FUNCTION option(VBAR) ms=MatchCondExpr {
    let last_exp = snd (List.hd (List.rev ms)) in
    let r = join_range start (range_of_exp last_exp) in
    FunExp (r, ("_match_arg", Impl, fresh_tyvar ()), MatchExp (r, Var (r, "_match_arg", ref []), ms))
    }

MatchExpr :
  | start=MATCH e=Expr WITH option(VBAR) ms=MatchCondExpr { 
    let last_exp = snd (List.hd (List.rev ms)) in
    let r = join_range start (range_of_exp last_exp) in
    MatchExp (r, e, ms) 
    }

MatchCondExpr :
  | m=MatchForm RARROW e=Expr %prec prec_match { [(m, e)] }
  | m=MatchForm RARROW e=Expr VBAR ms=MatchCondExpr { (m, e) :: ms }

MatchForm :
  | m1=LitMatchForm COMMA ms=separated_nonempty_list(COMMA, LitMatchForm) { MatchTuple (m1 :: ms) }
  | m1=MatchForm COLCOL m2=MatchForm { MatchCons (m1, m2) }
  | m=LitMatchForm { m }

LitMatchForm :
  | x=ID { MatchVar x.value }
  | i=INTV { MatchILit i.value }
  | TRUE   { MatchBLit true }
  | FALSE  { MatchBLit false }
  | LPAREN RPAREN { MatchULit }
  | LBRACKET ms=separated_list(SEMI, LitMatchForm) RBRACKET {
    let rec makelist l = match l with
      | h :: t -> MatchCons (h, makelist t)
      | [] -> MatchNil
    in makelist ms 
    }
  // | LPAREN m=MatchFormExpr COLON t=Type RPAREN { MatchAsc (m, t) }
  | LPAREN m=MatchForm RPAREN { m }
  | UNDER { MatchWild }

BelowSemiExpr :
  | IfExpr { $1 }
  | ForExpr { $1 }
  | WhileExpr { $1 }
  | PutExpr { $1 }

IfExpr :
  | start=IF e1=Expr THEN e2=NoSemiExpr ELSE e3=NoSemiExpr {
      let r = join_range start (range_of_exp e3) in
      IfExp (r, e1, e2, e3)
    }

ForExpr :
  | start=FOR i=ID EQ e1=Expr TO e2=Expr DO e3=Expr done_r=DONE {
      make_for (join_range start done_r) i.value e1 e2 `To e3
    }
  | start=FOR i=ID EQ e1=Expr DOWNTO e2=Expr DO e3=Expr done_r=DONE {
      make_for (join_range start done_r) i.value e1 e2 `Downto e3
    }

WhileExpr :
  | start=WHILE e1=Expr DO e2=Expr done_r=DONE {
      make_while (join_range start done_r) e1 e2
    }

PutExpr :
  | e1=PutExpr SUBSTITUTE e2=PutExpr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      SubstExp (r, e1, e2)
    }
  | e1=PostfixExpr DOT LPAREN e2=Expr RPAREN LARROW e3=PutExpr {
      let r = join_range (range_of_exp e1) (range_of_exp e3) in
      PutExp (r, e1, e2, e3)
    }
  | TupleExpr { $1 }

TupleExpr :
  | e1=BinOpExpr COMMA es=separated_nonempty_list(COMMA, BinOpExpr) {
      let r = List.fold_left (fun r e -> join_range r (range_of_exp e)) (range_of_exp e1) es in
      TupleExp (r, e1 :: es)
    }
  | e=BinOpExpr { e }
  
BinOpExpr :
  | e1=BinOpExpr op=Op e2=BinOpExpr {
      BinOp (join_range (range_of_exp e1) (range_of_exp e2), op, e1, e2)
    }
  | e1=BinOpExpr COLCOL e2=BinOpExpr {
      ConsExp (join_range (range_of_exp e1) (range_of_exp e2), e1, e2)
    }
  | UnaryExpr { $1 }

%inline Op :
  | PLUS { Plus }
  | MINUS { Minus }
  | STAR { Mult }
  | DIV { Div }
  | MOD { Mod }
  | LAND { And }
  | LOR { Or }
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }

UnaryExpr :
  | PLUS e=UnaryExpr { e }
  | start_r=MINUS e=UnaryExpr {
      let r = join_range start_r (range_of_exp e) in
      let zero = IConst (dummy_range, 0) in
      BinOp (r, Minus, zero, e)
    }
  | AppExpr { $1 }

AppExpr :
  | e1=AppExpr e2=PostfixExpr {
      AppExp (join_range (range_of_exp e1) (range_of_exp e2), e1, e2)
    }
  | start_r=REF e=PostfixExpr {
      let r = join_range start_r (range_of_exp e) in
      RefExp (r, e)
    }
  | start_r=MAKEARRAY e1=PostfixExpr e2=PostfixExpr {
      let r = join_range start_r (range_of_exp e2) in
      MakeArrayExp (r, e1, e2)
    }
  | start_r=LENGTHARRAY e=PostfixExpr {
      let r = join_range start_r (range_of_exp e) in
      LengthExp (r, e)
    }
  | PostfixExpr { $1 }

PostfixExpr :
  | e1=PostfixExpr DOT LPAREN e2=Expr end_r=RPAREN {
      let r = join_range (range_of_exp e1) end_r in
      GetExp (r, e1, e2)
    }
  | PrefixExpr { $1 } 

PrefixExpr :
  | start_r=BANG e=PrefixExpr {
      let r = join_range start_r (range_of_exp e) in
      DerefExp (r, e)
    }
  | SimpleExpr { $1 }

SimpleExpr :
  | i=INTV { IConst (i.range, i.value) }
  | r=TRUE { BConst (r, true) }
  | r=FALSE { BConst (r, false) }
  | start=LPAREN last=RPAREN {
      UConst (join_range start last)
    }
  | x=ID { Var (x.range, x.value, ref []) }
  | start=LPAREN e=Expr COLON u=Type last=RPAREN {
      AscExp (join_range start last, e, u)
    }
  | start=LBRACKET l=ListElms last=RBRACKET {
      l (join_range start last) 
    }
  | LPAREN e=Expr RPAREN { e }

ListElms :
  | /* empty */ { fun r -> NilExp(r, fresh_tyvar ()) }
  | e=BinOpExpr { fun r ->
      ConsExp(range_of_exp e, e, NilExp(r, fresh_tyvar ()))
    }
  | e=BinOpExpr SEMI l=ListElms { fun r ->
      ConsExp(range_of_exp e, e, l r)
    }

Type:
  | u1=Type RARROW u2=Type { TyFun (u1, u2) }
  | TupleType { $1 }
  
TupleType :
  | u1=PostType STAR us=separated_nonempty_list(STAR, PostType) { TyTuple (u1 :: us) }
  | PostType { $1 }

PostType :
  | u=PostType LIST { TyList u }
  | u=PostType REF { TyRef u }
  | u=PostType ARRAY { TyArray u }
  | SimpleType { $1 }

SimpleType :
  | INT { TyInt }
  | BOOL { TyBool }
  | UNIT { TyUnit }
  | QUESTION { TyDyn }
  | QUOTE x=ID {
      try
        Environment.find x.value !tyvenv
      with Not_found ->
        let u = fresh_tyvar () in
        tyvenv := Environment.add x.value u !tyvenv;
        u
    }
  // | LBRACKET u=Type RBRACKET { TyList u }
  | LPAREN u=Type RPAREN { u }
