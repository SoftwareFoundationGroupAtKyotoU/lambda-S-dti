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

def get_nested_type_slots(node):
    """(Int -> (Int -> Int)) 形式の型を末尾まで分解する"""
    if node.is_list and len(node.children) >= 3 and node.children[1].value == "->":
        return [node.children[0]] + get_nested_type_slots(node.children[2])
    return [node]

def analyze_ast(node, all_targets):
    """ASTを走査して変異ターゲットを特定。lambdaとdefine返り値を連動させる"""
    if not node.is_list: return

    is_define = (len(node.children) > 0 and node.children[0].value == "define")
    
    # benchmark関数は除外
    is_benchmark = False
    if is_define:
        try:
            header = node.children[1]
            if header.is_list and len(header.children) > 0:
                if header.children[0].value == "benchmark": is_benchmark = True
        except: pass

    if is_define and not is_benchmark:
        try:
            header = node.children[1]
            # 1. defineの引数 (例: takのx)
            if header.is_list and len(header.children) > 1:
                for arg_sexp in header.children[1:]:
                    if arg_sexp.is_list and len(arg_sexp.children) == 3 and arg_sexp.children[1].value == ":":
                        all_targets.append([arg_sexp.children[2]])

            # 2. defineの返り値型シグネチャのスロット
            ret_type_node = None
            for i, child in enumerate(node.children):
                if not child.is_list and child.value == ":":
                    ret_type_node = node.children[i + 1]
                    break
            
            type_slots = get_nested_type_slots(ret_type_node) if ret_type_node else []

            # 3. 内部の lambda 引数を再帰的に探索
            lambda_arg_types = []
            def find_lambdas(n):
                if not n.is_list or not n.children: return
                if n.children[0].value == "lambda":
                    arg_decl = n.children[1].children[0]
                    lambda_arg_types.append(arg_decl.children[2])
                for c in n.children: find_lambdas(c)
            find_lambdas(node)

            # 4. 同期リンク (lambda引数とシグネチャ位置を統合)
            for idx, lat in enumerate(lambda_arg_types):
                if idx < len(type_slots) - 1:
                    all_targets.append([lat, type_slots[idx]])
            
            # 5. 右端の返り値型
            if type_slots:
                all_targets.append([type_slots[-1]])

        except Exception as e: pass

    # 子要素を再帰探索
    if not is_benchmark: # benchmarkの中身は探索しない
        for child in node.children:
            analyze_ast(child, all_targets)

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
    compile_cmd = [
        "docker", "run", "--rm",
        "-v", f"{config_dir}:/src", "-w", "/src",
        DOCKER_IMAGE, GRIFT_CMD, "-O", "3", "-o", "bench", source_filename
    ]
    try:
        subprocess.run(compile_cmd, check=True, capture_output=True, text=True)
    except subprocess.CalledProcessError as e:
        # 詳細なコンパイルエラーを表示
        print(f"\n[Compile Error in {source_filename}]\n{e.stderr}")
        return {"status": "Compile Failed", "times": [], "stderr": e.stderr}

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
    except subprocess.CalledProcessError as e:
        print(f"\n[Runtime Error]\n{e.stderr}")
        return {"status": "Run Failed", "times": [], "stderr": e.stderr}

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

def main():
    parser = argparse.ArgumentParser(description="Run Grift Lattice Benchmark.")
    parser.add_argument("grift_path", help="Path to the .grift file")
    parser.add_argument("input_path", help="Path to the input text file")
    parser.add_argument("--static", action="store_true", help="Run only the fully-static version")
    parser.add_argument("-i", "--iter", type=int, default=500, help="Iterations")
    
    args = parser.parse_args()

    # パス検証
    grift_path = os.path.abspath(args.grift_path)
    input_path = os.path.abspath(args.input_path)
    if not os.path.exists(grift_path) or not os.path.exists(input_path):
        print("Error: File not found.")
        return

    filename = os.path.basename(grift_path)
    filename_no_ext = os.path.splitext(filename)[0]

    # 出力先特定
    try:
        latest_log_dir = get_latest_log_dir()
        suffix = "_fs" if args.static else ""
        output_jsonl_path = os.path.join(latest_log_dir, f"GRIFT_{filename_no_ext}{suffix}.jsonl")
    except Exception as e:
        print(f"Error setting up log directory: {e}")
        return

    # 入力準備
    with open(input_path, 'r') as f:
        multiplied_input = (f.read().strip() + "\n") * args.iter

    # AST解析
    with open(grift_path, 'r') as f:
        tokens = tokenize("(" + f.read() + ")")
    ast_root = parse(tokens)
    
    # define等のトップレベル要素のみ抽出
    definitions = [c for c in ast_root.children if c.is_list and len(c.children) > 0 and c.children[0].value in ["define", "module", "imports"]]
    ast_root.children = definitions

    all_targets = []
    for child in ast_root.children:
        analyze_ast(child, all_targets)
    
    total_variants = 2 ** len(all_targets)
    if args.static:
        variants_to_run = [0]
    else:
        # 動的型(ビットが1)の数が少ない順にソートする
        # 同じ数の場合は、インデックスの小さい順(辞書順)にする
        variants_to_run = sorted(range(total_variants), key=lambda x: (bin(x).count('1'), x))
    
    print(f"Total variants: {total_variants}")
    with open(output_jsonl_path, 'w') as f: pass

    work_dir = os.path.join(os.path.dirname(grift_path), f"experiments_{filename_no_ext}")
    os.makedirs(work_dir, exist_ok=True)

    # 実行ループ
    for i in variants_to_run:
        # すべて初期化してからビットに応じて適用
        for group in all_targets:
            for node in group: node.is_mutable_type = False
        
        config_id = ""
        for bit_idx in range(len(all_targets)):
            is_dyn = (i >> bit_idx) & 1
            config_id += "D" if is_dyn else "S"
            for node in all_targets[bit_idx]:
                node.is_mutable_type = is_dyn

        base_code = "\n".join([serialize(c) for c in ast_root.children])
        full_code = base_code + get_grift_driver_code(args.iter)
        
        variant_dir = os.path.join(work_dir, f"config_{i}")
        os.makedirs(variant_dir, exist_ok=True)
        with open(os.path.join(variant_dir, filename), 'w') as f:
            f.write(full_code)

        print(f"[{i+1}/{total_variants}] {config_id} ... ", end="", flush=True)
        result = run_benchmark(variant_dir, filename, multiplied_input)
        
        times = result.get("times", [])
        avg_time = sum(times) / len(times) if times else 0.0
        print(f"{result['status']} (Avg: {avg_time:.4f}s)")
        
        # ご指定の厳密なJSON構造
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

        with open(output_jsonl_path, 'a') as f:
            f.write(json.dumps(output_obj) + "\n")

    print(f"Done! Saved to: {output_jsonl_path}")

if __name__ == "__main__":
    main()