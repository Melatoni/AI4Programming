import os
import json
import re
import subprocess
from datasets import load_dataset
from openai import OpenAI

# ==================== 配置 ====================
# OpenAI/OpenRouter API 客户端
client = OpenAI(
    base_url="https://openrouter.ai/api/v1",
    api_key=os.getenv("OPENROUTER_API_KEY", "API-KEY")
)

# Frama-C 验证相关配置
# 注意：Frama-C路径在这里硬编码，请根据您的系统进行调整
FRAMA_C_PATH = os.path.expanduser("~/.opam/default/bin/frama-c")

# 生成策略配置
NUM_GENERATIONS_PER_TASK = 10  # 每个任务独立生成的最大次数
GENERATION_TEMPERATURE = 0.7   # 为独立生成设置更高的随机性，以获得多样化输出
MAX_SAMPLES_TO_PROCESS = 50    # 要处理的数据集样本数量

# 输出目录
OUTPUT_DIR = "verifiable_code_pass_at_k"

INITIAL_PROMPT_TEMPLATE = """
You are a world-class formal verification expert specializing in Frama-C and ACSL. Your mission is to convert a given algorithm description into a C code file that is 100% verifiable by Frama-C/WP.

Follow this expert verification strategy meticulously.

---
### I. C Code & Type Rules
1.  **No Standard Libraries**: DO NOT include `<stdio.h>`, `<stdlib.h>`, `<limits.h>`, or `<math.h>`. Frama-C has built-in knowledge. Use ACSL constants like `INT_MAX` directly if needed.
2.  **Use `int` for Booleans**: To avoid dependencies on `<stdbool.h>`, represent boolean logic using the `int` type. Use `1` for `true` and `0` for `false`.
3.  **Array Pointer Decay**: For array parameters `T arr[R][C]`, remember they decay to pointers `T (*arr)[C]`. Any axiomatic logic functions operating on them MUST use the correct pointer type for consistency.

---
### II. ACSL Logic & Annotation Rules
1.  **Recursive Logic for Complexity**: DO NOT use `\sum`. For complex logic like summations or properties over sequences, define a recursive `logic` function within an `axiomatic` block. Provide base and recursive axioms.
2.  **CRITICAL - Helper Axioms**: For recursive functions, you MUST add helper axioms (lemmas) to prove key properties that the prover cannot deduce on its own. For instance, if all elements are within a range, their sum is also within a derived range.
3.  **CRITICAL - `ensures` Clause for Boolean-like Functions**: For functions that return a boolean-like `int` (1 or 0), the `ensures` clause MUST use the logical equivalence operator `<==>`. This is the most robust and verifiable pattern. Example: `ensures (\exists integer i; ... ) <==> (\result == 1);`.
4.  **Mandatory Loop Annotations**: EVERY `for` or `while` loop MUST have:
    *   `loop invariant`: One or more concise and powerful invariants that capture the state of the loop.
    *   `loop variant`: A variant to prove termination (e.g., `n - i`).
5.  **Prevent Runtime Errors (RTE)**: Proactively prevent overflows. Add `requires` clauses to constrain inputs for operations like multiplication (`i * i`) or accumulation in loops.

---
### III. ACSL Syntax & Pitfall Rules
1.  **NO C-style Ternary in ACSL**: Inside ACSL annotations (`/*@ ... */`), NEVER use the C ternary operator `? :`. If conditional logic is needed, use the ACSL construct `if P then E1 else E2`.
2.  **No Parentheses around `if-then-else`**: The `if P then E1 else E2` construct is a complete term. DO NOT wrap it in extra parentheses, e.g., `\result == (if P...);` is WRONG.
3.  **Correct Range Syntax**: The range operator is `..` with NO SPACES around it (e.g., `0..n-1`).
4.  **No Stray Semicolons**: Avoid empty statements or extra semicolons inside ACSL annotations.

---
### IV. Golden Standard Example
Study this perfect, verifiable `is_not_prime` function. It demonstrates many of the rules above.

```c
/*@
  requires n >= 2;
  // Rule II.5: Prevents i*i overflow in the loop condition for 32-bit int.
  requires n <= 46340 * 46340; 
  
  assigns \nothing;
  
  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (\exists integer i; 2 <= i && i * i <= n && n % i == 0) <==> (\result == 1);
*/
int is_not_prime(int n) {{ // Rule I.2: Uses int, not bool.
    /*@
      loop invariant 2 <= i;
      loop invariant \forall integer k; 2 <= k < i ==> n % k != 0;
      loop assigns i;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant n - i;
    */
    for (int i = 2; i * i <= n; i++) {{
        if (n % i == 0) {{
            return 1; // Corresponds to the 'true' case of the ensures clause.
        }}
    }}
    return 0; // Corresponds to the 'false' case of the ensures clause.
}}

### V. Your Task
Now, apply all these rules to solve the following problem. Provide only the complete, verifiable C code with all necessary ACSL annotations. Do not add any explanatory text before or after the code block.

Problem Description:
{task_description}
"""

# ==================== 辅助函数 ====================

def load_dataset_data():
    """从Hugging Face Hub加载MBPP数据集。"""
    try:
        ds = load_dataset("Muennighoff/mbpp", "full", token=False, download_mode="force_redownload", trust_remote_code=True)
        print("数据集加载成功。")
        return ds["test"]
    except Exception as e:
        print(f"错误：加载数据集失败: {e}")
        return None

def clean_generated_code(raw_code):
    """
    更健壮地清理从LLM返回的原始代码字符串。
    它会找到第一个有效的代码块并提取它，丢弃所有前导的解释性文本。
    """
    # 1. 寻找代码的真正起点
    # 代码可能以 #define, #include, /*@, 或基本类型/关键字开头
    code_start_patterns = [
        r'/\*@',          # ACSL block
        r'#define',        # Macro definition
        r'#include',       # Include statement (just in case)
        r'\b(int|void|char|float|double|struct|enum|typedef)\b' # Common C keywords
    ]
    
    start_pos = -1
    for pattern in code_start_patterns:
        match = re.search(pattern, raw_code)
        if match:
            # 找到第一个匹配的位置
            pos = match.start()
            if start_pos == -1 or pos < start_pos:
                start_pos = pos

    if start_pos != -1:
        # 从找到的第一个代码标记开始截取
        code = raw_code[start_pos:]
    else:
        # 如果找不到任何标记，就退回到原来的清理方式
        code = raw_code

    # 2. 移除Markdown代码块标记
    cleaned_code = re.sub(r'^```[a-zA-Z]*\n?', '', code, flags=re.MULTILINE)
    cleaned_code = re.sub(r'```$', '', cleaned_code, flags=re.MULTILINE)  

    # 3. 移除在Frama-C验证中通常不必要的头文件
    cleaned_code = re.sub(r'#include\s*<(stdio\.h|stdlib\.h|string\.h)>\n?', '', cleaned_code)
    
    return cleaned_code.strip()

def get_opam_environment():
    """获取并返回包含opam环境变量的字典，以正确运行Frama-C。"""
    try:
        result = subprocess.run(
            ["opam", "env", "--shell", "sh"],
            capture_output=True, text=True, check=True, encoding="utf-8"
        )
        opam_env = {}
        for line in result.stdout.splitlines():
            if line.startswith("export "):
                var_part = line[len("export "):]
                var_name, var_value = var_part.split("=", 1)
                opam_env[var_name.strip()] = var_value.strip().strip("'\"")
        
        merged_env = os.environ.copy()
        merged_env.update(opam_env)
        return merged_env
    except Exception as e:
        print(f"警告：获取opam环境变量失败: {e}。将尝试使用系统默认环境。")
        return os.environ.copy()

def verify_with_frama_c(file_path):
    """使用Frama-C验证给定的C文件。"""
    if not os.path.exists(file_path):
        return False, f"文件不存在: {file_path}"
    
    if not os.path.exists(FRAMA_C_PATH):
        return False, f"Frama-C未找到，请检查路径配置: {FRAMA_C_PATH}"
    
    opam_env = get_opam_environment()
    command = [
        FRAMA_C_PATH,
        "-wp",
        "-wp-prover", "alt-ergo,z3",
        "-wp-timeout", "10",
        file_path
    ]
    
    try:
        result = subprocess.run(
            command,
            capture_output=True, text=True, encoding="utf-8",
            timeout=60, env=opam_env
        )
        
        if result.returncode == 0:
            return True, "验证成功"
        else:
            error_msg = f"验证失败 (返回码 {result.returncode}):\n{result.stderr}\n{result.stdout}"
            return False, error_msg
    except Exception as e:
        return False, f"执行Frama-C时发生异常: {str(e)}"

# ==================== 核心逻辑 ====================

def generate_and_verify_all_tasks(dataset, prompt_template, output_dir, max_samples):
    """
    为数据集中的每个任务独立生成多次代码并进行验证 (Pass@k策略)。
    只要有一次验证成功，该任务就算成功。
    """
    os.makedirs(output_dir, exist_ok=True)
    results_log = []

    if not dataset:
        print("错误：数据集为空，无法处理。")
        return

    for i, item in enumerate(dataset):
        if i >= max_samples:
            print(f"已达到最大处理样本数 ({max_samples})，停止执行。")
            break

        task_description = item["text"]
        task_id = item.get("task_id", i)
        print(f"\n----- 正在处理样本 #{task_id}: {task_description[:60].replace(chr(10), ' ')}... -----")

        is_verified_for_task = False
        final_file_path = ""
        last_error_for_task = ""
        
        for generation_attempt in range(NUM_GENERATIONS_PER_TASK):
            print(f"  第 {generation_attempt + 1}/{NUM_GENERATIONS_PER_TASK} 次尝试 (任务 #{task_id})...")
            
            try:
                prompt = prompt_template.format(task_description=task_description)
                response = client.chat.completions.create(
                    model="google/gemini-2.5-flash",
                    messages=[{"role": "user", "content": prompt}],
                    temperature=GENERATION_TEMPERATURE,
                )
                
                raw_code = response.choices[0].message.content
                generated_code = clean_generated_code(raw_code)

                filename = f"sample_{task_id:04d}_generation_{generation_attempt}.c"
                file_path = os.path.join(output_dir, filename)
                with open(file_path, "w", encoding='utf-8') as f:
                    f.write(f"// Task ID: {task_id}\n// Generation: {generation_attempt}\n\n{generated_code}\n")

                print(f"  正在使用Frama-C验证 {filename}...")
                is_verified, verification_output = verify_with_frama_c(file_path)

                if is_verified:
                    print(f"  ✅ 成功: 第 {generation_attempt + 1} 次尝试验证通过！")
                    is_verified_for_task = True
                    final_file_path = file_path
                    break  # 成功后，跳出当前任务的生成循环
                else:
                    print(f"  ❌ 失败: 第 {generation_attempt + 1} 次尝试验证失败。")
                    last_error_for_task = verification_output
            
            except Exception as e:
                print(f"  ❌ 错误: 在第 {generation_attempt + 1} 次尝试中发生API或其它错误: {e}")
                last_error_for_task = str(e)
                continue

        final_status = "verified" if is_verified_for_task else "failed_after_all_generations"
        results_log.append({
            "sample_id": task_id,
            "task": task_description,
            "final_status": final_status,
            "total_generations": generation_attempt + 1,
            "final_code_path": final_file_path if is_verified_for_task else "N/A",
            "last_error": "" if is_verified_for_task else last_error_for_task
        })
        print(f"----- 样本 #{task_id} 处理完成，最终状态: {final_status} -----")

    log_path = os.path.join(output_dir, "generation_log.json")
    with open(log_path, "w", encoding='utf-8') as f:
        json.dump(results_log, f, indent=2, ensure_ascii=False)
    print(f"\n所有任务处理完毕。结果日志已保存至: {log_path}")

# ==================== 执行入口 ====================

if __name__ == "__main__":
    dataset = load_dataset_data()
    if dataset:
        generate_and_verify_all_tasks(
            dataset=dataset,
            prompt_template=INITIAL_PROMPT_TEMPLATE,
            output_dir=OUTPUT_DIR,
            max_samples=MAX_SAMPLES_TO_PROCESS
        )

