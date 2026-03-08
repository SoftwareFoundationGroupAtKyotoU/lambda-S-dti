import subprocess
import json
import time
import os
import re
import sys
import argparse
import shutil
import itertools
import concurrent.futures # 並列処理用に追加

# ================= 設定エリア =================
DOCKER_IMAGE = "grift"
GRIFT_CMD = "/root/.racket/7.2/bin/grift"
LOG_BASE_DIR = "/app/logs" # ログ保存先のベースディレクトリ
# ============================================

# --- (SExp, tokenize, parse, serialize, get_nested_type_slots, is_referenced, analyze_ast は変更なし) ---
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
    if sexp.is_mutable_type: 
        return "Dyn"

    if sexp.is_list:
        inner = " ".join([serialize(c) for c in sexp.children])
        if len(sexp.children) >= 2 and str(sexp.children[1]) == ":":
            return f"[{inner}]"
        return f"({inner})"
    else:
        return sexp.value

def get_nested_type_slots(node):
    if node.is_list and len(node.children) >= 3 and node.children[1].value == "->":
        return [node.children[0]] + get_nested_type_slots(node.children[2])
    return [node]

def is_referenced(node, target_name):
    if not node.is_list:
        return node.value == target_name
    for child in node.children:
        if is_referenced(child, target_name):
            return True
    return False

def analyze_ast(node, fun_targets, fix_dom_targets, fix_ret_targets):
    if not node.is_list: return

    is_define = (len(node.children) > 0 and node.children[0].value == "define")
    is_benchmark = False
    func_name = ""
    if is_define:
        try:
            header = node.children[1]
            if header.is_list and len(header.children) > 0:
                func_name = header.children[0].value
                if func_name in ["benchmark", "empty-list", "cons", "is-empty", "head", "tail"]: 
                    is_benchmark = True
        except: pass

    if is_define and not is_benchmark:
        try:
            header = node.children[1]
            define_args = []
            if header.is_list and len(header.children) > 1:
                for arg_sexp in header.children[1:]:
                    if arg_sexp.is_list and len(arg_sexp.children) == 3 and arg_sexp.children[1].value == ":":
                        define_args.append(arg_sexp.children[2])

            ret_type_node = None
            ret_type_idx = -1
            for i, child in enumerate(node.children):
                if not child.is_list and child.value == ":":
                    ret_type_node = node.children[i + 1]
                    ret_type_idx = i + 1
                    break
            
            type_slots = get_nested_type_slots(ret_type_node) if ret_type_node else []
            body_nodes = node.children[ret_type_idx + 1:] if ret_type_idx != -1 else []

            lambda_arg_types = []
            def find_lambdas(n):
                if not n.is_list or not n.children: return
                if n.children[0].value == "lambda":
                    arg_decl = n.children[1].children[0]
                    lambda_arg_types.append(arg_decl.children[2])
                for c in n.children: find_lambdas(c)
            find_lambdas(node)
            
            lambda_pairs = []
            for idx, lat in enumerate(lambda_arg_types):
                if idx < len(type_slots) - 1:
                    lambda_pairs.append([lat, type_slots[idx]])
                else:
                    lambda_pairs.append([lat])
            
            is_recursive_def = False
            if func_name:
                for b_node in body_nodes:
                    if is_referenced(b_node, func_name):
                        is_recursive_def = True
                        break

            if not is_recursive_def:
                for arg in reversed(define_args): fun_targets.append([arg])
                for pair in reversed(lambda_pairs): fun_targets.append(pair)
            else:
                if define_args: fix_dom_targets.append([define_args[0]])
                if type_slots: fix_ret_targets.append([type_slots[-1]])
                for pair in reversed(lambda_pairs): fun_targets.append(pair)
                if len(define_args) > 1:
                    for arg in reversed(define_args[1:]): fun_targets.append([arg])

        except Exception as e: pass

    if not is_benchmark:
        for child in node.children:
            analyze_ast(child, fun_targets, fix_dom_targets, fix_ret_targets)

def get_grift_driver_code(loop_count):
    return f"""
;; --- Auto-generated Loop Driver ---
(define (run-benchmark-loop [k : Int]) : Unit
  (if (<= k 0)
      () 
      (begin
        (time (benchmark))
        (run-benchmark-loop (- k 1)))))
(run-benchmark-loop {loop_count})
"""

def parse_all_grift_times(stdout_str):
    matches = re.findall(r"time \(sec\):\s*([\d\.]+)", stdout_str)
    return [float(m) for m in matches]

def parse_grift_profiler(stdout_str):
    cast_total = None
    longest_data = None
    for line in stdout_str.split('\n'):
        if "total casts:" in line:
            parts = line.split("total casts:")[1].split()
            total = sum(int(p) for p in parts if p.isdigit())
            cast_total = total
        elif "longest proxy chain:" in line:
            parts = line.split("longest proxy chain:")[1].split()
            if parts and parts[0].isdigit():
                longest_data = int(parts[0])
    return cast_total, longest_data

def get_latest_log_dir():
    log_base = os.path.expanduser(LOG_BASE_DIR)
    if not os.path.exists(log_base):
        raise FileNotFoundError(f"Log base directory does not exist: {log_base}")
    subdirs = [d for d in os.listdir(log_base) if os.path.isdir(os.path.join(log_base, d))]
    pattern = re.compile(r"^\d{8}-\d{2}:\d{2}:\d{2}$")
    valid_subdirs = sorted([d for d in subdirs if pattern.match(d)])
    if not valid_subdirs:
        raise FileNotFoundError(f"No timestamped directories found in {log_base}")
    return os.path.join(log_base, valid_subdirs[-1])

# =====================================================================
# コンパイル・実行処理の分割（並列化のため）
# =====================================================================

def compile_variant(task):
    """1つのミュータント（バリアント）の全コンパイル処理を行う関数"""
    config_dir, source_perf, source_prof, c_code_dir, dest_c_filename = task

    abs_source_perf = os.path.abspath(os.path.join(config_dir, source_perf))
    abs_source_prof = os.path.abspath(os.path.join(config_dir, source_prof))

    # 1. GRIFT Perf コンパイル (デフォルトバックエンドでバイナリ生成)
    cmd_perf = [GRIFT_CMD, "-O", "3", "-o", os.path.abspath(os.path.join(config_dir, "bench_perf")), abs_source_perf]
    
    # 2. GRIFT Prof コンパイル (プロファイラ付きバイナリ生成)
    cmd_prof = [GRIFT_CMD, "-O", "3", "--cast-profiler", "-o", os.path.abspath(os.path.join(config_dir, "bench_prof")), abs_source_prof]
    
    # 3. GRIFT C バックエンド コンパイル (自動でCコンパイルまで行われ、実行バイナリが生成される)
    cmd_c_bin = [GRIFT_CMD, "--backend", "C", "-O", "3", "-o", os.path.abspath(os.path.join(config_dir, "bench_c_perf")), abs_source_perf]

    # 4. ログディレクトリ保存用の Cコード(.c) だけを抽出するコマンド
    cmd_gen_c = [GRIFT_CMD, "--backend", "C", "--keep-ir", dest_c_filename, source_perf]

    errors = []
    # 実行バイナリのコンパイル実行
    for cmd in [cmd_perf, cmd_prof, cmd_c_bin]:
        try:
            subprocess.run(cmd, cwd=config_dir, check=True, capture_output=True, text=True)
        except subprocess.CalledProcessError as e:
            errors.append(f"Command failed: {' '.join(cmd)}\n{e.stderr}")

    # 保存用Cコードの生成と GRIFT ディレクトリへの移動
    try:
        subprocess.run(cmd_gen_c, cwd=config_dir, check=True, capture_output=True, text=True)
        src_c = os.path.join(config_dir, dest_c_filename)
        dest_c = os.path.join(c_code_dir, dest_c_filename) # Cコードは無事に GRIFT フォルダへ保存されます
        
        if os.path.exists(src_c):
            shutil.move(src_c, dest_c)
        else:
            c_files = [f for f in os.listdir(config_dir) if f.endswith(".c")]
            if c_files: shutil.move(os.path.join(config_dir, c_files[0]), dest_c)
    except subprocess.CalledProcessError as e:
        errors.append(f"C Code Gen failed\n{e.stderr}")

    return {"status": "success" if not errors else "error", "errors": errors, "config_dir": config_dir}

def execute_compiled_binary(config_dir, bin_name, input_content, is_profiler=False):
    """コンパイル済みバイナリを実行して結果を取得する関数"""
    abs_bin_path = os.path.abspath(os.path.join(config_dir, bin_name))
    
    if not os.path.exists(abs_bin_path):
        return {"status": "Compile Failed (Binary missing)", "times": [], "cast": None, "longest": None}

    try:
        proc = subprocess.run([abs_bin_path], input=input_content, cwd=config_dir, check=True, capture_output=True, text=True)
        stdout_str = proc.stdout.strip()
        
        result = {"status": "Success"}
        if is_profiler:
            cast_data, longest_data = parse_grift_profiler(stdout_str)
            result["cast"] = cast_data
            result["longest"] = longest_data
        else:
            times = parse_all_grift_times(stdout_str)
            result["status"] = "Success" if len(times) > 0 else "No Output"
            result["times"] = times
        return result
    except subprocess.CalledProcessError as e:
        return {"status": "Run Failed", "times": [], "cast": None, "longest": None, "stderr": e.stderr}

def main():
    parser = argparse.ArgumentParser(description="Run Grift Lattice Benchmark.")
    parser.add_argument("grift_path", help="Path to the .grift file")
    parser.add_argument("input_path", help="Path to the input text file")
    parser.add_argument("--static", action="store_true", help="Run only the fully-static version")
    parser.add_argument("-i", "--iter", type=int, default=500, help="Iterations")
    
    args = parser.parse_args()

    grift_path = os.path.abspath(args.grift_path)
    input_path = os.path.abspath(args.input_path)
    if not os.path.exists(grift_path) or not os.path.exists(input_path):
        print("Error: File not found.")
        return

    filename = os.path.basename(grift_path)
    filename_no_ext = os.path.splitext(filename)[0]

    try:
        latest_log_dir = get_latest_log_dir()
        suffix = "_fs" if args.static else ""
        output_jsonl_path = os.path.join(latest_log_dir, f"GRIFT_{filename_no_ext}{suffix}.jsonl")
        output_jsonl_path_c = os.path.join(latest_log_dir, f"GRIFTC_{filename_no_ext}{suffix}.jsonl")
        c_code_dir = os.path.join(latest_log_dir, "GRIFT")
        os.makedirs(c_code_dir, exist_ok=True)
        
        with open(output_jsonl_path, 'w') as f: pass 
        with open(output_jsonl_path_c, 'w') as f: pass 
    except Exception as e:
        print(f"Error setting up log directory: {e}")
        return

    with open(input_path, 'r') as f:
        base_input = f.read().strip()
        multiplied_input_perf = (base_input + "\n") * (args.iter + 10)
        multiplied_input_prof = (base_input + "\n") * (1 + 10)

    # AST解析
    with open(grift_path, 'r') as f:
        tokens = tokenize("(" + f.read() + ")")
    ast_root = parse(tokens)
    
    definitions = [c for c in ast_root.children if c.is_list and len(c.children) > 0 and c.children[0].value in ["define", "module", "imports"]]
    ast_root.children = definitions

    fun_targets, fix_dom_targets, fix_ret_targets = [], [], []
    for child in ast_root.children:
        analyze_ast(child, fun_targets, fix_dom_targets, fix_ret_targets)
    
    all_targets = fun_targets + fix_dom_targets + fix_ret_targets
    total_variants = 2 ** len(all_targets)
    
    if args.static:
        variants_to_run = [0]
    else:
        variants_to_run = [0]
        elements = list(range(len(all_targets)))
        for k in range(1, len(all_targets) + 1):
            for comb in itertools.combinations(elements, k):
                val = 0
                for bit in comb: val |= (1 << bit)
                variants_to_run.append(val)
    
    print(f"Total variants: {total_variants}")

    work_dir = os.path.join(os.path.dirname(grift_path), f"experiments_{filename_no_ext}")
    os.makedirs(work_dir, exist_ok=True)

    # ================= Phase 1: ファイル生成とコンパイル（並列処理） =================
    compile_tasks = []
    run_tasks = [] # 実行用の情報を保持

    for seq_idx, i in enumerate(variants_to_run):
        for group in all_targets:
            for node in group: node.is_mutable_type = False
        
        config_id = ""
        for bit_idx in range(len(all_targets)):
            is_dyn = (i >> bit_idx) & 1
            config_id += "D" if is_dyn else "S"
            for node in all_targets[bit_idx]: node.is_mutable_type = is_dyn

        base_code = "\n".join([serialize(c) for c in ast_root.children])
        variant_dir = os.path.join(work_dir, f"config_{i}")
        os.makedirs(variant_dir, exist_ok=True)
        mutant_index = seq_idx + 1

        # ソースファイルの書き出し
        filename_perf = f"perf_{filename}"
        filename_prof = f"prof_{filename}"
        dest_c_filename = f"{filename_no_ext}{mutant_index}.c"

        with open(os.path.join(variant_dir, filename_perf), 'w') as f:
            f.write(base_code + get_grift_driver_code(args.iter))
        with open(os.path.join(variant_dir, filename_prof), 'w') as f:
            f.write(base_code + get_grift_driver_code(1))

        compile_tasks.append((variant_dir, filename_perf, filename_prof, c_code_dir, dest_c_filename))
        run_tasks.append((variant_dir, mutant_index, config_id, base_code))

    print("コンパイルを並列で実行中...")
    start_time = time.time()
    
    # ThreadPoolExecutor でサブプロセスを並列化（プロセス数は自動調整）
    with concurrent.futures.ThreadPoolExecutor() as executor:
        compile_results = list(executor.map(compile_variant, compile_tasks))

    # エラーチェック
    for res in compile_results:
        if res["status"] == "error":
            print(f"[Warning] Compile errors in {res['config_dir']}:\n" + "\n".join(res["errors"]))
            
    print(f"コンパイル完了 (所要時間: {time.time() - start_time:.2f}秒)\n")

    # ================= Phase 2: バイナリの実行と計測（直列処理で正確に） =================
    print("実行フェーズを開始します...")
    for variant_dir, mutant_index, config_id, base_code in run_tasks:
        print(f"[{mutant_index}/{total_variants}] {config_id} ... ", end="", flush=True)

        # 1. パフォーマンス計測 (GRIFT)
        res_perf = execute_compiled_binary(variant_dir, "bench_perf", multiplied_input_perf, is_profiler=False)
        times = res_perf.get("times", [])
        avg_time = sum(times) / len(times) if times else 0.0

        # 2. プロファイル計測 (GRIFT)
        res_prof = execute_compiled_binary(variant_dir, "bench_prof", multiplied_input_prof, is_profiler=True)
        print(f"  -> GRIFT  : {res_perf['status']} (Avg: {avg_time:.4f}s)")

        output_obj = {
            "mode": "GRIFT",
            "mutant_index": mutant_index,
            "after_mutate": base_code,
            "after_insertion": None,
            "after_translation": None,
            "times_sec": times,
            "mem": None,
            "cast": res_prof.get("cast"),       
            "inference": None,
            "longest": res_prof.get("longest")  
        }
        with open(output_jsonl_path, 'a') as f:
            f.write(json.dumps(output_obj) + "\n")

        # 3. パフォーマンス計測 (GRIFTC)
        res_c = execute_compiled_binary(variant_dir, "bench_c_perf", multiplied_input_perf, is_profiler=False)
        times_c = res_c.get("times", [])
        avg_time_c = sum(times_c) / len(times_c) if times_c else 0.0
        print(f"  -> GRIFTC : {res_c['status']} (Avg: {avg_time_c:.4f}s)")

        output_obj_c = {
            "mode": "GRIFTC",
            "mutant_index": mutant_index,
            "after_mutate": base_code,
            "after_insertion": None,
            "after_translation": None,
            "times_sec": times_c,
            "mem": None,
            "cast": None,
            "inference": None,
            "longest": None
        }
        with open(output_jsonl_path_c, 'a') as f:
            f.write(json.dumps(output_obj_c) + "\n")

    print(f"\nDone! Saved to: {latest_log_dir}")

    if os.path.exists(work_dir):
        shutil.rmtree(work_dir)
        print(f"Cleaned up temporary directory: {work_dir}")

if __name__ == "__main__":
    main()