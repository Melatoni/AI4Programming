# Verifiable C Code Generation with LLMs and Frama-C

This project explores the capabilities of Large Language Models (LLMs) in generating C code that is formally verifiable using the Frama-C static analysis platform. The primary goal is to assess how well modern LLMs can adhere to the strict syntactic and semantic rules of C and its associated specification language, ACSL (ANSI/ISO C Specification Language).

## 🚀 Overview

The core of this project is a Python script that automates the following workflow:
1.  **Loads a Task**: Fetches a programming problem from the [MBPP (Mostly Basic Python Programming) dataset](https://huggingface.co/datasets/mbpp).
2.  **Generates Code**: Feeds the task description into a large language model (e.g., Google's Gemini) with a highly detailed prompt outlining expert-level rules for writing verifiable C code.
3.  **Verifies with Frama-C**: Attempts to formally verify the generated C code using the Frama-C/WP (Weakest Precondition) plugin.
4.  **Implements Pass@k Strategy**: For each task, the script makes multiple generation attempts (`k` times) and considers the task "solved" if any one of the generations successfully passes Frama-C verification.
5.  **Logs Results**: Records the outcome (verified or failed), the number of attempts, the final verifiable code, and any error messages in a structured JSON log.

## 🛠️ Technology Stack

-   **Language**: Python 3
-   **LLM API**: [OpenRouter](https://openrouter.ai/) (for accessing models like Google Gemini)
-   **Formal Verification Tool**: [Frama-C](https://frama-c.com/) (specifically the WP plugin with Alt-Ergo and Z3 provers)
-   **Dataset**: [Muennighoff/mbpp](https://huggingface.co/datasets/Muennighoff/mbpp) from Hugging Face
-   **Python Libraries**: `openai`, `datasets`, `subprocess`

## 📋 Prerequisites

Before running the script, ensure you have the following installed and configured:

1.  **Python 3**:
    ```bash
    pip install openai datasets
    ```

2.  **Frama-C and Provers**: The easiest way to install Frama-C is via `opam`.
    ```bash
    # Install opam (package manager for OCaml)
    # See: https://opam.ocaml.org/doc/Install.html

    # Initialize opam
    opam init

    # Install Frama-C and the required provers
    opam install frama-c alt-ergo z3
    ```
    **Note**: The script hardcodes the Frama-C path. You may need to adjust `FRAMA_C_PATH` in the Python script to match your system's path (e.g., `~/.opam/default/bin/frama-c`).

3.  **API Key**: The script requires an API key from OpenRouter. Set it as an environment variable:
    ```bash
    export OPENROUTER_API_KEY="your-api-key-here"
    ```

## ⚙️ How to Run

1.  Clone this repository:
    ```bash
    git clone https://github.com/YourUsername/YourRepositoryName.git
    cd YourRepositoryName
    ```

2.  Ensure all prerequisites are met.

3.  Execute the main script:
    ```bash
    python your_script_name.py
    ```

The script will create an output directory named `verifiable_code_pass_at_k/`, which will contain all generated `.c` files and a final `generation_log.json` summary.

## 📊 Results and Analysis

*(This is where you present your findings. Be concise but informative.)*

The experiment was run on the first 50 samples from the MBPP dataset. The results are summarized in `verifiable_code_pass_at_k/generation_log.json`.

-   **Overall Success Rate**: **XX / 50** tasks were successfully verified (a XX% success rate).
-   **Average Attempts for Success**: For the verified tasks, the average number of generation attempts was **X.X**.
