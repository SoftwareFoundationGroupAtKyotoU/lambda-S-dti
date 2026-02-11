import subprocess
import json
import time
import os
import re
import sys
import argparse
import shutil

# ================= 設定エリア =================
DOCKER_IMAGE = "grift"
GRIFT_CMD = "/root/.racket/7.2/bin/grift"
LOG_BASE_DIR = "~/lambda-S-dti/logs" # ログ保存先のベースディレクトリ
# ============================================

class SExp:
    def __init__(self, value, is_list=False, children=None):
        self.value = value
        self.is_list = is_list
        self.children = children if children is not None else []
        self.is_mutable_type = False 

    def __repr__(self):
        if self.is_list: return "(" + " ".join([str(c) for c in self.children]) + ")"
        return self.value

def tokenize(text):
    text = re.sub(r';.*', '', text)
    text = text.replace('(', ' ( ').replace(')', ' ) ')
    text = text.replace('[', ' ( ').replace(']', ' ) ')
    return text.split()

def parse(tokens):
    if not tokens: raise SyntaxError("Unexpected EOF")
    token = tokens.pop(0)
    if token == '(':
        children = []
        while tokens[0] != ')':
            children.append(parse(tokens))
        tokens.pop(0)
        return SExp(None, is_list=True, children=children)
    elif token == ')': raise SyntaxError("Unexpected )")
    else: return SExp(token, is_list=False)

def serialize(sexp):
    if sexp.is_list:
        inner = " ".join([serialize(c) for c in sexp.children])
        if len(sexp.children) >= 2 and str(sexp.children[1]) == ":":
            return f"[{inner}]"
        return f"({inner})"
    else:
        if sexp.is_mutable_type: return "Dyn"
        return sexp.value

def analyze_ast(node, fun_targets, fix_targets):
    """ASTを走査して変異箇所を特定 (benchmark関数は除外)"""
    is_define = (node.is_list and len(node.children) > 0 and node.children[0].value == "define")
    
    # フィルタリング: benchmark 関数なら変異対象にしない
    is_benchmark = False
    if is_define:
        try:
            header = node.children[1]
            if header.is_list and len(header.children) > 0:
                func_name = header.children[0].value
                if func_name == "benchmark":
                    is_benchmark = True
        except: pass

    # Fix Return Type
    if is_define and not is_benchmark:
        try:
            for i, child in enumerate(node.children):
                if not child.is_list and child.value == ":":
                    if i + 1 < len(node.children):
                        fix_targets.append(node.children[i + 1])
                    break
        except: pass

    # Recurse
    if node.is_list:
        for child in node.children:
            analyze_ast(child, fun_targets, fix_targets)
            
    # Fun Args
    if is_define and not is_benchmark:
        try:
            header = node.children[1]
            if header.is_list and len(header.children) > 1:
                for arg_sexp in header.children[1:]:
                    if arg_sexp.is_list and len(arg_sexp.children) == 3 and arg_sexp.children[1].value == ":":
                        fun_targets.append(arg_sexp.children[2])
        except: pass

def get_grift_driver_code(loop_count):
    code = f"""
;; --- Auto-generated Loop Driver ---
(define (run-benchmark-loop [k : Int]) : Unit
  (if (<= k 0)
      () 
      (begin
        (time (benchmark))
        (run-benchmark-loop (- k 1)))))
(run-benchmark-loop {loop_count})
"""
    return code

def parse_all_grift_times(stdout_str):
    matches = re.findall(r"time \(sec\):\s*([\d\.]+)", stdout_str)
    return [float(m) for m in matches]

def run_benchmark(config_dir, source_filename, input_content_multiplied):
    # コンパイル
    compile_cmd = [
        "docker", "run", "--rm",
        "-v", f"{config_dir}:/src", "-w", "/src",
        DOCKER_IMAGE, GRIFT_CMD, "-O", "3", "-o", "bench", source_filename
    ]
    try:
        subprocess.run(compile_cmd, check=True, capture_output=True)
    except subprocess.CalledProcessError:
        return {"status": "Compile Failed", "times": []}

    # 実行
    run_cmd = [
        "docker", "run", "--rm", "-i",
        "-v", f"{config_dir}:/src", "-w", "/src",
        DOCKER_IMAGE, "./bench"
    ]
    
    try:
        proc = subprocess.run(run_cmd, input=input_content_multiplied, check=True, capture_output=True, text=True)
        stdout_str = proc.stdout.strip()
        times = parse_all_grift_times(stdout_str)
        status = "Success" if len(times) > 0 else "No Output"
        return {"status": status, "times": times, "stdout": stdout_str}

    except subprocess.CalledProcessError:
        return {"status": "Run Failed", "times": []}

def get_latest_log_dir():
    """最新のログディレクトリパスを取得する"""
    log_base = os.path.expanduser(LOG_BASE_DIR)
    
    if not os.path.exists(log_base):
        raise FileNotFoundError(f"Log base directory does not exist: {log_base}")

    try:
        subdirs = [d for d in os.listdir(log_base) if os.path.isdir(os.path.join(log_base, d))]
    except OSError as e:
        raise OSError(f"Error accessing log directory: {e}")

    # YYYYMMDD-hh:mm:ss 形式のみ抽出
    pattern = re.compile(r"^\d{8}-\d{2}:\d{2}:\d{2}$")
    valid_subdirs = [d for d in subdirs if pattern.match(d)]

    if not valid_subdirs:
        raise FileNotFoundError(f"No timestamped directories found in {log_base}")

    valid_subdirs.sort()
    return os.path.join(log_base, valid_subdirs[-1])

def main():
    parser = argparse.ArgumentParser(description="Run Grift Lattice Benchmark with specific input file.")
    parser.add_argument("grift_path", help="Path to the .grift file")
    parser.add_argument("input_path", help="Path to the input text file")
    
    # オプション引数
    parser.add_argument("--static", action="store_true", help="Run only the fully-static version without mutants")
    parser.add_argument("-i", "--iter", type=int, default=500, help="Number of iterations (default: 500)")
    
    args = parser.parse_args()

    # 1. パス検証
    grift_path = os.path.abspath(args.grift_path)
    input_path = os.path.abspath(args.input_path)
    loop_count = args.iter # 繰り返し回数を取得

    if not os.path.exists(grift_path):
        print(f"Error: Grift file not found: {grift_path}")
        return
    if not os.path.exists(input_path):
        print(f"Error: Input file not found: {input_path}")
        return

    filename = os.path.basename(grift_path)
    filename_no_ext = os.path.splitext(filename)[0]
    base_dir = os.path.dirname(grift_path)

    # 2. 出力先（最新ログディレクトリ）の特定
    try:
        latest_log_dir = get_latest_log_dir()
        
        suffix = "_fs" if args.static else ""
        output_filename = f"GRIFT_{filename_no_ext}{suffix}.jsonl"
        output_jsonl_path = os.path.join(latest_log_dir, output_filename)
        
        print(f"Target Grift : {filename}")
        print(f"Target Input : {os.path.basename(input_path)}")
        print(f"Iterations   : {loop_count}")
        if args.static:
            print("Mode         : STATIC ONLY")
        print(f"Output JSONL : {output_jsonl_path}")
        
    except Exception as e:
        print(f"Error setting up log directory: {e}")
        return

    # 3. 入力ファイルの読み込みと増幅
    with open(input_path, 'r') as f:
        raw_input = f.read().strip()
    input_data_for_one_run = raw_input + "\n"
    multiplied_input = input_data_for_one_run * loop_count

    # 4. 作業用ディレクトリ
    work_dir = os.path.join(base_dir, f"experiments_{filename_no_ext}")
    if not os.path.exists(work_dir):
        os.makedirs(work_dir)

    # 5. AST解析 & フィルタリング
    with open(grift_path, 'r') as f:
        raw = f.read()
    tokens = tokenize("(" + raw + ")")
    ast_root = parse(tokens)
    
    definitions = []
    for child in ast_root.children:
        if child.is_list and len(child.children) > 0:
            head = child.children[0].value
            if head in ["define", "module", "imports", "require", "provide"]:
                definitions.append(child)
    ast_root.children = definitions

    fun_targets = []
    fix_targets = []
    for child in ast_root.children:
        analyze_ast(child, fun_targets, fix_targets)
    
    all_targets = fun_targets + fix_targets
    total_variants_possible = 2 ** len(all_targets)
    
    # 実行するバリエーションの決定
    if args.static:
        variants_to_run = [0]
    else:
        variants_to_run = range(total_variants_possible)
    
    print(f"Total variants possible: {total_variants_possible}")
    print(f"Running variants: {len(variants_to_run)}")
    print("-" * 40)

    # 出力ファイル初期化
    with open(output_jsonl_path, 'w') as f: pass

    # 6. Lattice Loop
    for i in variants_to_run:
        # 変異適用
        for t in all_targets: t.is_mutable_type = False
        config_id_list = []
        for bit_idx in range(len(all_targets)):
            is_dyn = (i >> bit_idx) & 1
            if is_dyn:
                all_targets[bit_idx].is_mutable_type = True
                config_id_list.append("D")
            else:
                config_id_list.append("S")
        config_id = "".join(config_id_list)

        # 変異後コード生成
        base_code = "\n".join([serialize(c) for c in ast_root.children])
        driver_code = get_grift_driver_code(loop_count)
        full_code = base_code + driver_code
        
        # コンパイル用ファイル書き出し
        variant_dir = os.path.join(work_dir, f"config_{i}")
        if not os.path.exists(variant_dir): os.makedirs(variant_dir)
        
        with open(os.path.join(variant_dir, filename), 'w') as f:
            f.write(full_code)

        print(f"[{i+1}/{total_variants_possible}] {config_id} ... ", end="", flush=True)
        
        # 実行
        result = run_benchmark(variant_dir, filename, multiplied_input)
        
        times = result.get("times", [])
        avg_time = sum(times) / len(times) if times else 0.0
        print(f"{result['status']} (Avg: {avg_time:.4f}s)")
        
        output_obj = {
            "mode": "GRIFT",
            "mutant_index": i + 1,
            "after_mutate": base_code,
            "after_insertion": None,
            "after_translation": None,
            "times_sec": times,
            "mem": None,
            "cast": None,
            "inference": None,
            "longest": None
        }

        # ログ出力
        with open(output_jsonl_path, 'a') as f:
            f.write(json.dumps(output_obj) + "\n")

    print(f"Done! Results saved to: {output_jsonl_path}")

if __name__ == "__main__":
    main()