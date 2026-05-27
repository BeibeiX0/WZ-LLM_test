import os
from pathlib import Path

os.environ["CUDA_VISIBLE_DEVICES"] = "1"

# Project root resolved relative to this file: python/utils/Constant4_25.py -> ../../
PROJECT_ROOT = Path(__file__).resolve().parents[2]
TIME_OUT = 300
NUM_CPUS = 1
'''Number of CPU processes to use'''

USE_MAPLE = False
GENERATE_LEMMA = True
GPU_AVAILABLE_COUNT = 1 # torch.cuda.device_count() 
'''Number of available GPUs'''
CONTEXTUAl = False
'''Whether to use contextual model inference'''

MODEL_ACTOR_GPU_USAGE = 0.9
'''GPU memory fraction per model actor, should be slightly larger than the GPU memory fraction in vllm config'''

MODLE_PATH = os.environ.get("WZ_MODEL_PATH", "")
VLLM_CONFIG = {
    "model": MODLE_PATH, # model path
    "max_model_len": 4096, # maximum token length for model input
    "gpu_memory_utilization": 0.9, # GPU memory utilization fraction
    "swap_space": 4.0, # swap space per GPU in GB
    "trust_remote_code": True, # whether to trust remote repository model code
    "tensor_parallel_size": 1, # number of GPUs for distributed inference
    "dtype": "bfloat16", # model floating-point data type
}
'''VLLM model loading parameters, see vllm.LLM function for details'''


SAMPLE_CONFIG = {
    "n": 16, # number of samples
    "temperature": 0.7, # sampling temperature
    "max_tokens": 2048, # maximum number of output tokens
    "logprobs": 0,
}
'''VLLM sampling parameters for inference, see vllm.SamplingParams function for details'''
# PROMPT_CONFIG = {
#     "system": "You are using Lean4 for theorem proving", # system prompt
#     "instruction": "",
#     "input": "",
#     "prompt_template": # $ts is the placeholder for theorem proof state; the program will replace $ts with the current proof state
#         f'''You are proving a theorem in Lean 4.\nBased on the current state of the theorem, provide the most reasonable proof tactic.\nEnsure that the tactic you provide is syntactically correct according to Lean 4's tactic syntax and is effective in progressing the proof.\n\n
#     [Current State]: $ts\n[Output Tactic]: \n'''
# }
USE_DEEPSEEK = False 
PROMPT_CONFIG = {
    "system": "You are using Lean4 for theorem proving", # system prompt
    "instruction": "",
    "input": "",
    "prompt_template": # $ts is the placeholder for theorem proof state; the program will replace $ts with the current proof state
        f'''You are proving a theorem in Lean 4.\nBased on the current state of the theorem (which is enclosed in <state></state>), provide the most reasonable proof tactic.\nEnsure that the tactic you provide (which should be enclosed in <tactic></tactic>) is syntactically correct according to Lean 4's tactic syntax and is effective in progressing the proof.\n<state>$ts</state>\n\n'''
}
'''Prompt parameters for model inference'''
DEEPSEEK_PROMPT_CONFIG = {
    "system": "", # system prompt
    "instruction": "",
    "input": "",
    "prompt_template": # $ts is the placeholder for theorem proof state; the program will replace $ts with the current proof state
        f"""Complete the following Lean 4 code:
$ts
"""
}

DEEPSEEK_PASSK = 32
DEEPSEEK_SAMPLE_CONFIG = {
    "n": 1, # number of samples
    "temperature": 0.95, # sampling temperature
    "max_tokens": 2048, # maximum output tokens
    "logprobs": 0,
}

LEAN_WORK_DIR = str(PROJECT_ROOT)
REPL_VERSION = "4.25"
Contextual_TOP_K = 2
VERBOSE = True
LEMMA_NEZERO_PATH = str(PROJECT_ROOT / "python" / "lemmas" / "nezero_lemmas.jsonl")
LEMMA_RECURSIVE_PATH = str(PROJECT_ROOT / "python" / "lemmas" / "recursive_lemmas.jsonl")
IMPORT_CONTENT = \
"""import Mathlib

open Real Nat Finset BigOperators Polynomial

set_option maxHeartbeats 8000000000"""
LEMMA_NEZERO_DICT = {
    "(choose n k : ℝ) ≠ 0": "norm_cast\nsuffices 0 < choose n k by linarith\nexact cast_pos.2 (Nat.choose_pos (by linarith))",
    "¬m ! = 0": "exact Nat.factorial_ne_zero m",
    "((↑n + 1 - ↑k): ℝ) ≠ 0": "suffices 0 < (↑n + 1 - ↑k :ℝ ) by linarith\nsimp\nnorm_cast\nlinarith",
    "((-↑n + ↑k - 1) : ℝ) ≠ 0": "suffices 0 > (-↑n + ↑k - 1 :ℝ ) by linarith\nsimp\nnorm_cast\nlinarith",
    "((↑k + 1 - ↑n - 1) : ℝ) ≠ 0": "suffices 0 > (k - ↑n : ℝ) by linarith\nsimp\nnorm_cast",
    "(((2 * n).choose n) : ℝ) ≠ 0": "suffices 0 < (((2 * n).choose n) : ℝ) by linarith\nexact cast_pos.2 (Nat.choose_pos (by linarith))",
    "(2 * ↑k + 1 : ℝ) ≠ 0": "linarith",
    "((2 * (↑k + 1) + 1) : ℝ) ≠ 0": "norm_cast",
    "((-1) ^ k : ℝ) ≠ 0": "norm_num",
    "(n + 1 - k : ℝ) ≠ 0": "suffices 0 < (↑n + 1 - ↑k :ℝ ) by linarith\nsimp\nnorm_cast\nlinarith",
    "(2 * n - 2 * k).choose (n - k) ≠ 0": "suffices 0 < (2 * n - 2 * k).choose (n - k) by linarith\nexact Nat.choose_pos (by omega)",
    "¬catalan (n - k) = 0": "by_cases h : k = n\nrw [h]\nnorm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]\nrw [catalan_eq_centralBinom_div]\n  h1 :n - k + 1 ≠ 0 := by linarith\nfield_simp\n  h2 :n - k + 1 ≤ 2 * (n - k) := by\n  rw [two_mul]\n  simp only [add_le_add_iff_left]\n  suffices k < n by omega\n  exact lt_of_le_of_ne (by linarith) h\nsuffices 2 * (n - k) ≤ (2 * (n - k)).choose (n - k) by exact le_trans h2 this\nnth_rw 1 [← choose_one_right (2 * (n - k))]\nrw [← centralBinom_eq_two_mul_choose (n - k)]\nexact Nat.choose_le_centralBinom 1 (n - k)",
    "((2 * (k + 1) + 1) : ℝ) ≠ 0": "norm_cast",
    "n - k + 1 ≠ 0": "linarith",
    "((2*k).choose k : ℝ) ≠ 0": "suffices 0 < ((2*k).choose k : ℝ) by linarith\nnorm_cast\nexact Nat.choose_pos (by linarith)",
    
    "(catalan (n - k) : ℝ) ≠ 0": """    by_cases h : k = n
    · rw [h]
      norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

    · rw [catalan_eq_centralBinom_div]
      have h1 :n - k + 1 ≠ 0 := by
        linarith
      field_simp
      have h2 :n - k + 1 ≤  2 * (n - k) := by
        rw [two_mul]
        simp only [add_le_add_iff_left]
        suffices k < n by omega
        exact lt_of_le_of_ne (by linarith) h
      suffices 2 * (n - k) ≤ (2 * (n - k)).choose (n - k) by exact le_trans h2 this
      nth_rw 1 [← choose_one_right (2 * (n - k))]
      rw [← centralBinom_eq_two_mul_choose (n - k)]
      exact Nat.choose_le_centralBinom 1 (n - k)""",
      
    "(-(2 * ↑n) + 2 * ↑k + 1 : ℝ) ≠ 0": "suffices 1 + 2 * ↑k < (2 * ↑n : ℝ) by linarith\nnorm_cast\nlinarith",
    "(k + 1 : ℝ) ≠ 0": "linarith",
    "(↑k + 1 : ℝ) ≠ 0": "linarith",
    "(↑n - ↑k + 1 : ℝ) ≠ 0": "suffices n >= (k + 1 : ℝ) by linarith\nnorm_cast",
    "(-↑n - 2 + ↑k : ℝ) ≠ 0": "suffices 2 + n > (k : ℝ) by linarith\nnorm_cast\nlinarith",
    "(↑n - ↑k + 2 : ℝ) ≠ 0": "suffices 2 + n > (k : ℝ) by linarith\nnorm_cast\nlinarith",
    "(↑n - ↑k + 1 : ℝ) ≠ 0": "suffices 1 + n > (k : ℝ) by linarith\nnorm_cast\nlinarith",
    "(2 * n + 1).choose n ≠ 0": "norm_cast\nsuffices 0 < (2 * n + 1).choose n by linarith\nexact Nat.choose_pos (by linarith)",
    "↑((2 * n + 1).choose n : ℝ) ≠ 0": "suffices 0 < (2 * n + 1).choose n by linarith\nexact Nat.choose_pos (by linarith)",
    "(↑n + 1 : ℝ) ≠ 0": "norm_cast",
    "(↑n + 1 + ↑1 : ℝ) ≠ 0": "norm_cast",
    "(-↑n - 1 + ↑k : ℝ) ≠ 0": "suffices 0 < (↑n + 1 - ↑k : ℝ) by linarith\nsimp\nnorm_cast\nlinarith",
    "(-↑n - 2 + (↑k + 1) : ℝ) ≠ 0": "suffices n + 2 > (k + 1 : ℝ) by linarith\nnorm_cast\nnorm_num\nomega",
    "((2 * ↑n + 3) : ℝ) ≠ 0": "linarith",
    "(n + 1 : ℝ) ≠ 0": "linarith",
    "(k + 1 : ℝ) ≠ 0": "linarith",
    "(-(2 * ↑n) + 2 * ↑k + 1 : ℝ) ≠ 0": "suffices 1 + 2 * ↑k < (2 * ↑n : ℝ) by linarith\nnorm_cast\nlinarith",
    "(-↑n - 2 + ↑n : ℝ) ≠ 0": "suffices 2 + n > (n : ℝ) by linarith\nlinarith",
    "(2 * m + 1).choose m ≠ 0": "suffices 0 < (2 * m + 1).choose m by linarith\nexact Nat.choose_pos (by linarith)",
    "(2 * k).choose k ≠ 0": "suffices 0 < (2 * k).choose k by linarith\nexact Nat.choose_pos (by linarith)"
}
LEMMA_NEZERO_LIST = [
    """linarith""","""norm_cast""",""""norm_num""",
    """suffices 0 < (2 * k).choose k by linarith\nexact Nat.choose_pos (by linarith)""",
    """suffices 1 + 2 * ↑k < (2 * ↑n : ℝ) by linarith\nnorm_cast\nlinarith""",
    """suffices n >= (k + 1 : ℝ) by linarith\nnorm_cast""",
    """suffices 2 + n > (k : ℝ) by linarith\nnorm_cast\nlinarith""",
    """suffices 1 + n > (k : ℝ) by linarith\nnorm_cast\nlinarith""",
    """suffices 0 < (2 * n + 1).choose n by linarith\nexact Nat.choose_pos (by linarith)""",
    """norm_cast\nsuffices 0 < (2 * n + 1).choose n by linarith\nexact Nat.choose_pos (by linarith)""",
    """suffices n + 2 > (k + 1 : ℝ) by linarith\nnorm_cast\nnorm_num\nomega""",
    """suffices 1 + 2 * ↑k < (2 * ↑n : ℝ) by linarith\nnorm_cast\nlinarith""",
    """    by_cases h : k = n
    · rw [h]
      norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

    · rw [catalan_eq_centralBinom_div]
      have h1 :n - k + 1 ≠ 0 := by
        linarith
      field_simp
      have h2 :n - k + 1 ≤  2 * (n - k) := by
        rw [two_mul]
        simp only [add_le_add_iff_left]
        suffices k < n by omega
        exact lt_of_le_of_ne (by linarith) h
      suffices 2 * (n - k) ≤ (2 * (n - k)).choose (n - k) by exact le_trans h2 this
      nth_rw 1 [← choose_one_right (2 * (n - k))]
      rw [← centralBinom_eq_two_mul_choose (n - k)]
      exact Nat.choose_le_centralBinom 1 (n - k)""",
      """
suffices 0 < (2 * m + 1).choose m by linarith\nexact Nat.choose_pos (by linarith)
      """,
      """suffices 0 < ((2*k).choose k : ℝ) by linarith\nnorm_cast\nexact Nat.choose_pos (by linarith)"""

]
LEMMA_NEZERO_LIST = LEMMA_NEZERO_DICT.keys()
LEMMA_RECURSIVE_LIST = ["rw [centralBinom_succ k]", "rw [catalan_n_sub_k_succ hnk]", "rw [test hnk]"
                        , "rw [two_succ_choose_eq]", "rw [centralBinom_succ]", "rw [choose_ksucc n k (by linarith)]", "rw [choose_nsucc n k (by linarith)]"
                        , "rw [← neg_one_mul_n_succ_subk]"] 


FIXED_1 = \
"""
  --Fixed lemmas below
  have ne_zeroB':  ∀ {n} : ℕ, (B {n} : ℝ) * (B ({n} + 1) : ℝ)  ≠ 0 := by
    intro m
    rw [mul_ne_zero_iff]
    exact And.intro (ne_zeroB m) (ne_zeroB (m + 1))

  have ne_zeroAB' : ∀ {n} {k} : ℕ,  {k} < {n} → (B {n} : ℝ) * (A {n} {k} : ℝ) ≠ 0 := by
    intro {n} {k} hidx
    rw [mul_ne_zero_iff]
    exact And.intro (ne_zeroB {n}) (ne_zeroA {n} {k} hidx)

  have l₁ : ∀ {n} {k} : ℕ,  {k} < {n} → A ({n} + 1) {k} * B {n} / (B {n} * A {n} {k})  = A ({n} + 1) {k} / A {n} {k} := by
    intro {n} {k} hidx
    field_simp [ne_zeroA, ne_zeroB]
  have l₂ :∀ {n} {k} : ℕ,  {k} < {n} →  B ({n} + 1) * A {n} {k} / (B {n} * A {n} {k})  =  B ({n} + 1) / B {n} := by
    intro {n} {k} hidx
    field_simp [ne_zeroA, ne_zeroB]
  have r₁ :∀ {n} {k} : ℕ,  {k} < {n} → B ({n} + 1) * (R {n} ({k} + 1) * A {n} ({k} + 1)) / (B {n} * A {n} {k})  = R {n} ({k} + 1) * (A {n} ({k} + 1) / A {n} {k}) * (B ({n} + 1) / B {n}) := by
    intro {n} {k} hidx
    field_simp [ne_zeroA, ne_zeroB]
  have r₂ :∀ {n} {k} : ℕ,  {k} < {n} → B ({n} + 1) * (A {n} {k} * R {n} {k}) / (B {n} * A {n} {k}) = R {n} {k} *  (B ({n} + 1) / B {n}) := by
    intro {n} {k} hidx
    field_simp [ne_zeroA, ne_zeroB]

  have WZ_aux ({n} : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (ne_zero : ∀ {n} : ℕ, (B {n} : ℝ) ≠ 0) :
        ∑ {k} ∈ Finset.range ({n}{num}), (f {n} {k} / B {n} : ℝ) = (1 : ℝ) ↔ ∑ {k} ∈ Finset.range ({n}{num}), f {n} {k} = B {n} := by
    constructor
    ·  intro h
       rw [← Finset.sum_div, div_eq_iff (ne_zero {n}), one_mul] at h
       norm_cast at h
    ·  intro _
       rw [← Finset.sum_div, div_eq_iff (ne_zero {n}), one_mul]
       norm_cast

  have Step1 := WZ_aux {n} A B ne_zeroB
  --Use the above directly
"""
FIXED_1_WITH_PRIMISE = \
"""
  --Fixed lemmas below
  have ne_zeroB':  ∀ {n} : ℕ, {primise} → (B {n} : ℝ) * (B ({n} + 1) : ℝ)  ≠ 0 := by
    intro m hm
    rw [mul_ne_zero_iff]
    exact And.intro (ne_zeroB m hm) (ne_zeroB_succ m hm)

  have ne_zeroAB' : ∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → (B {n} : ℝ) * (A {n} {k} : ℝ) ≠ 0 := by
    intro {n} {k} hidx
    rw [mul_ne_zero_iff]
    exact And.intro (ne_zeroB {n} (by omega)) (ne_zeroA {n} {k} (by omega))

  have l₁ : ∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → A ({n} + 1) {k} * B {n} / (B {n} * A {n} {k})  = A ({n} + 1) {k} / A {n} {k} := by
    intro {n} {k} hidx
    field_simp [ne_zeroA {n} {k} ⟨hidx.1 ,hidx.2⟩, ne_zeroB {n} hidx.2]
  have l₂ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} →  B ({n} + 1) * A {n} {k} / (B {n} * A {n} {k})  =  B ({n} + 1) / B {n} := by
    intro {n} {k} hidx
    field_simp [ne_zeroA {n} {k} ⟨hidx.1 ,hidx.2⟩, ne_zeroB {n} hidx.2]
  have r₁ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → B ({n} + 1) * (R {n} ({k} + 1) * A {n} ({k} + 1)) / (B {n} * A {n} {k})  = R {n} ({k} + 1) * (A {n} ({k} + 1) / A {n} {k}) * (B ({n} + 1) / B {n}) := by
    intro {n} {k} hidx
    field_simp [ne_zeroA {n} {k} ⟨hidx.1 ,hidx.2⟩, ne_zeroB {n} hidx.2]
  have r₂ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → B ({n} + 1) * (A {n} {k} * R {n} {k}) / (B {n} * A {n} {k}) = R {n} {k} *  (B ({n} + 1) / B {n}) := by
    intro {n} {k} hidx
    field_simp [ne_zeroA {n} {k} ⟨hidx.1 ,hidx.2⟩, ne_zeroB {n} hidx.2]

  have WZ_aux ({n} : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (h : {primise}) (ne_zero : ∀ {n} : ℕ, {primise} → (B {n} : ℝ) ≠ 0) :
        ∑ {k} ∈ Finset.range ({n}{num}), (f {n} {k} / B {n} : ℝ) = (1 : ℝ) ↔ ∑ {k} ∈ Finset.range ({n}{num}), f {n} {k} = B {n} := by
    constructor
    ·  intro hi
       rw [← Finset.sum_div, div_eq_iff (ne_zero {n} h), one_mul] at hi
       norm_cast at h
    ·  intro _
       rw [← Finset.sum_div, div_eq_iff (ne_zero {n} h), one_mul]
       norm_cast

  have Step1 := WZ_aux {n} A B (by omega) ne_zeroB
  --Use the above directly
"""
FIXED_STEP2_PREFIX_WITH_PRIMISE = \
"""
  have ne_zeroB : ∀ {n} : ℕ, {primise} → (B {n} : ℝ)  ≠ 0 := by sorry
  have ne_zeroB_succ : ∀ {n} : ℕ, {primise} → (B ({n} + 1) : ℝ)  ≠ 0 := by sorry
  have ne_zeroA :∀ {n} {k} : ℕ, {k} < {n} ∧ {primise} → (A {n} {k} : ℝ) ≠ 0 := by sorry
  have ne_zeroB':  ∀ {n} : ℕ, {primise} → (B {n} : ℝ) * (B ({n} + 1) : ℝ)  ≠ 0 := by sorry
  have ne_zeroAB' : ∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → (B {n} : ℝ) * (A {n} {k} : ℝ) ≠ 0 := by sorry
  have l₁ : ∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → A ({n} + 1) {k} * B {n} / (B {n} * A {n} {k})  = A ({n} + 1) {k} / A {n} {k} := by sorry
  have l₂ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} →  B ({n} + 1) * A {n} {k} / (B {n} * A {n} {k})  =  B ({n} + 1) / B {n} := by sorry
  have r₁ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → B ({n} + 1) * (R {n} ({k} + 1) * A {n} ({k} + 1)) / (B {n} * A {n} {k})  = R {n} ({k} + 1) * (A {n} ({k} + 1) / A {n} {k}) * (B ({n} + 1) / B {n}) := by sorry
  have r₂ :∀ {n} {k} : ℕ,  {k} < {n} ∧ {primise} → B ({n} + 1) * (A {n} {k} * R {n} {k}) / (B {n} * A {n} {k}) = R {n} {k} *  (B ({n} + 1) / B {n}) := by sorry
  have WZ_aux ({n} : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (h : {primise}) (ne_zero : ∀ {n} : ℕ, (B {n} : ℝ) ≠ 0) : ∑ {k} ∈ Finset.range ({n}{num}), (f {n} {k} / B {n} : ℝ) = (1 : ℝ) ↔ ∑ {k} ∈ Finset.range ({n}{num}), f {n} {k} = B {n} := by sorry
  have aux₁ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → A {n} ({k} + 1) / A {n} {k} = {AKdiv} := by sorry
  have aux₂ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → A ({n} + 1) {k} / A {n} {k} = {Adiv} := by sorry
  have aux₃ :∀ {n} : ℕ, {primise} → B ({n} + 1) / B {n} = {Bdiv} := by sorry
  have aux₄ :∀ {n} : ℕ, {primise} → A ({n} + 1) ({n} {num}) = ({Anndiv}) * A {n} ({n}{num2}):= by sorry
  have aux₅ :∀ {n} : ℕ, {primise} → A ({n} + 1) ({n} {num2}) = ({A_nadd1_n_div}) * A {n} ({n}{num2}):= by sorry
"""
FIXED_STEP2_PREFIX = \
"""
  have ne_zeroB : ∀ {n} : ℕ, (B {n} : ℝ)  ≠ 0 := by sorry
  have ne_zeroA :∀ {n} {k} : ℕ, {k} < {n} → (A {n} {k} : ℝ) ≠ 0 := by sorry
  have ne_zeroB_succ : ∀ {n} : ℕ, (B ({n} + 1) : ℝ)  ≠ 0 := by sorry
  have ne_zeroB':  ∀ {n} : ℕ, (B {n} : ℝ) * (B ({n} + 1) : ℝ)  ≠ 0 := by sorry
  have ne_zeroAB' : ∀ {n} {k} : ℕ,  {k} < {n} → (B {n} : ℝ) * (A {n} {k} : ℝ) ≠ 0 := by sorry
  have l₁ : ∀ {n} {k} : ℕ,  {k} < {n} → A ({n} + 1) {k} * B {n} / (B {n} * A {n} {k})  = A ({n} + 1) {k} / A {n} {k} := by sorry
  have l₂ :∀ {n} {k} : ℕ,  {k} < {n} →  B ({n} + 1) * A {n} {k} / (B {n} * A {n} {k})  =  B ({n} + 1) / B {n} := by sorry
  have r₁ :∀ {n} {k} : ℕ,  {k} < {n} → B ({n} + 1) * (R {n} ({k} + 1) * A {n} ({k} + 1)) / (B {n} * A {n} {k})  = R {n} ({k} + 1) * (A {n} ({k} + 1) / A {n} {k}) * (B ({n} + 1) / B {n}) := by sorry
  have r₂ :∀ {n} {k} : ℕ,  {k} < {n} → B ({n} + 1) * (A {n} {k} * R {n} {k}) / (B {n} * A {n} {k}) = R {n} {k} *  (B ({n} + 1) / B {n}) := by sorry
  have WZ_aux ({n} : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (ne_zero : ∀ {n} : ℕ, (B {n} : ℝ) ≠ 0) : ∑ {k} ∈ Finset.range ({n}{num}), (f {n} {k} / B {n} : ℝ) = (1 : ℝ) ↔ ∑ {k} ∈ Finset.range ({n}{num}), f {n} {k} = B {n} := by sorry
  have aux₁  ({n} {k} : ℕ) (hnk : {k} < {n}): A {n} ({k} + 1) / A {n} {k} = {AKdiv} := by sorry
  have aux₂  ({n} {k} : ℕ) (hnk : {k} < {n}): A ({n} + 1) {k} / A {n} {k} = {Adiv} := by sorry
  have aux₃ :∀ {n} : ℕ, B ({n} + 1) / B {n} = {Bdiv} := by sorry
  have aux₄ :∀ {n} : ℕ, A ({n} + 1) ({n}{num}) = ({Anndiv}) * A {n} ({n}{num2}) := by sorry
  have aux₅ :∀ {n} : ℕ, A ({n} + 1) ({n}{num2}) = ({A_nadd1_n_div}) * A {n} ({n}{num2}) := by sorry
"""
FIXED_STEP2_PREFIX_WITH_PRIMISE_Bn0 = \
"""
  have aux₁ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → A {n} ({k} + 1) = ({AKdiv}) * A {n} {k} := by sorry
  have aux₂ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → A ({n} + 1) {k} = ({Adiv}) * A {n} {k} := by sorry
  have aux₃ :∀ {n} : ℕ, {primise} → A ({n} + 1) ({n} + 1) = ({Anndiv}) * A {n} {n} := by sorry
  have aux₄ :∀ {n} : ℕ, {primise} → A ({n} + 1) {n} = ({A_nadd1_n_div}) * A {n} {n} := by sorry
"""
FIXED_STEP2_PREFIX_Bn0 = \
"""
  have aux₁  ({n} {k} : ℕ) (hnk : {k} < {n}): A {n} ({k} + 1) = ({AKdiv}) * A {n} {k} := by sorry
  have aux₂  ({n} {k} : ℕ) (hnk : {k} < {n}): A ({n} + 1) {k} = ({Adiv}) * A {n} {k} := by sorry
  have aux₃ :∀ {n} : ℕ,  A ({n} + 1) ({n} + 1) = ({Anndiv}) * A {n} {n} := by sorry
  have aux₄ :∀ {n} : ℕ,  A ({n} + 1) {n} = ({A_nadd1_n_div}) * A {n} {n} := by sorry
"""
FIXED_2 = \
"""
  have Step2 : ∀ {n} : ℕ, f ({n} + 1) - f {n} = 0 := by
    intro {n}
    have WZ ({k} : ℕ) (htotalNumidx:{k} < {n}) : F ({n} + 1) {k} - F {n} {k} = G {n} ({k} + 1) - G {n} {k} := by
      simp only [F, G]
      field_simp [ne_zeroA, ne_zeroB, ne_zeroB_succ]
      rw [← div_left_inj' (ne_zeroAB' {n} {k} (by omega))]
      rw [sub_div, mul_sub, sub_div ]
      rw [l₁ {n} {k} (by omega), l₂ {n} {k} (by omega), r₁ {n} {k} (by omega), r₂ {n} {k} (by omega)]
      rw [sub_eq_iff_eq_add, ← sub_mul]

      nth_rw 2 [show B ({n} + 1) / B {n} = 1 * (B ({n} + 1) / B {n}) by grind]
      rw [← add_mul]
      simp [R]

      rw [aux₁ {n} {k} (by linarith), aux₂ {n} {k} (by linarith), aux₃ {n}]

      field_simp
"""
FIXED_2_Bn0 = \
"""
  have Step2 : ∀ {n} : ℕ,  f ({n} + 1) - f {n} = 0 := by
    intro {n}
    have WZ ({k} : ℕ) (htotalNumidx:{k} < {n}) : A ({n} + 1) {k} - A {n} {k} = G {n} ({k} + 1) - G {n} {k} := by
      simp only [G, R] -- bh
      rw [aux₁ {n} {k} htotalNumidx, aux₂ {n} {k} htotalNumidx]
"""
FIXED_2_WITH_PRIMISE = \
"""
  have Step2 : ∀ {n} : ℕ, {primise} → f ({n} + 1) - f {n} = 0 := by
    intro {n} primise
    have WZ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → F ({n} + 1) {k} - F {n} {k} = G {n} ({k} + 1) - G {n} {k} := by
      intro {n} {k} htotalNumidx
      simp only [F, G]
      field_simp [ne_zeroA {n} {k} (by omega), ne_zeroB {n} (by omega), ne_zeroB_succ {n} (by omega)]
      rw [← div_left_inj' (ne_zeroAB' {n} {k} (by omega))]
      rw [sub_div, mul_sub, sub_div]
      rw [l₁ {n} {k} (by omega), l₂ {n} {k} (by omega), r₁ {n} {k} (by omega), r₂ {n} {k} (by omega)]
      rw [sub_eq_iff_eq_add, ← sub_mul]
      nth_rw 2 [show B ({n} + 1) / B {n} = 1 * (B ({n} + 1) / B {n}) by grind]
      rw [← add_mul]
      simp [R]
      rw [aux₁ {n} {k} (by omega), aux₂ {n} {k} (by omega), aux₃ {n} (by omega)]
      field_simp
"""
FIXED_2_WITH_PRIMISE_Bn0 = \
"""
  have Step2 : ∀ {n} : ℕ, {primise}  → f ({n} + 1) - f {n} = 0 := by
    intro {n} primise
    have WZ : ∀ {n} {k} : ℕ, {k} < {n} ∧ {primise} →  A ({n} + 1) {k} - A {n} {k} = G {n} ({k} + 1) - G {n} {k} := by
      intro {n} {k} htotalNumidx
      simp only [G, R] -- bh
      rw [aux₁ {n} {k} htotalNumidx, aux₂ {n} {k} htotalNumidx]
"""
FIXED_3 = \
"""
  have Step3 : ∀ {n} : ℕ, f {n} = 1 := by
    intro m
    induction' m with m hm
    ·  simp [f, F, A, B]
    · exact (sub_eq_zero.1 $ Step2 m).trans hm
  unfold A B at Step1

  rw [Step1.1]

  exact Step3 {n}
"""
FIXED_3_WITH_PRIMISE = \
"""
  have Step3 : ∀ {n} : ℕ,  {primise} → f {n} = 1 := by
    intro wzm hm
    induction' hm with wzm hm ih
    · simp [f, F, A, B]
      simp [Finset.sum_range_succ]
      norm_num
    · exact (sub_eq_zero.1 $ Step2 wzm).trans ih
  unfold A B at Step1

  rw [Step1.1]

  exact Step3 {n} {name}
"""
FIXED_WZ_TACTIC = \
"""
    simp only [F, G]
    field_simp [ne_zeroA, ne_zeroB, ne_zeroB_succ]
    rw [← div_left_inj' (ne_zeroAB' {n} {k} (by omega))]
    rw [sub_div, mul_sub, sub_div ]
    rw [l₁ {n} {k} (by omega), l₂ {n} {k} (by omega), r₁ {n} {k} (by omega), r₂ {n} {k} (by omega)]
    rw [sub_eq_iff_eq_add, ← sub_mul]
    nth_rw 2 [show B ({n} + 1) / B {n} = 1 * (B ({n} + 1) / B {n}) by grind]
    rw [← add_mul]
    simp [R]
    rw [aux₁ {n} {k} (by linarith), aux₂ {n} {k} (by linarith), aux₃ {n}]
    field_simp
"""
FIXED_WZ_TACTIC_WITH_PRIMISE = \
"""
    intro {n} {k} htotalNumidx
    simp only [F, G]
    field_simp [ne_zeroA {n} {k} (by omega), ne_zeroB {n} (by omega), ne_zeroB_succ {n} (by omega)]
    rw [← div_left_inj' (ne_zeroAB' {n} {k} (by omega))]
    rw [sub_div, mul_sub, sub_div]
    rw [l₁ {n} {k} (by omega), l₂ {n} {k} (by omega), r₁ {n} {k} (by omega), r₂ {n} {k} (by omega)]
    rw [sub_eq_iff_eq_add, ← sub_mul]
    nth_rw 2 [show B ({n} + 1) / B {n} = 1 * (B ({n} + 1) / B {n}) by grind]
    rw [← add_mul]
    simp [R]
    rw [aux₁ {n} {k} (by omega), aux₂ {n} {k} (by omega), aux₃ {n} (by omega)]
    field_simp
"""
FIXED_WZ_TACTIC_Bn0 = \
"""
    simp only [G, R]
    rw [aux₁ {n} {k} htotalNumidx, aux₂ {n} {k} htotalNumidx]
"""
FIXED_WZ_TACTIC_WITH_PRIMISE_Bn0 = \
"""
    intro {n} {k} htotalNumidx
    simp only [G, R]
    rw [aux₁ {n} {k} htotalNumidx, aux₂ {n} {k} htotalNumidx]
"""

FIXED_CALC_TACTIC_LIST = ["intro {n}",
"have WZ ({k} : ℕ) (htotalNumidx:{k} < {n}) : F ({n} + 1) {k} - F {n} {k} = G {n} ({k} + 1) - G {n} {k} := by sorry",
"""
calc f ({n} + 1) - f {n}
  _ = (∑ {k} ∈ range ({n}{num1}), (F ({n} + 1) {k} - F {n} {k})) + F ({n} + 1) ({n}{num1}) := by
    simp [f]
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
  _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    {calc_rw}
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
    congr 2
    apply Finset.sum_congr rfl
    intro {k} hidx
    simp only [mem_range] at hidx
    exact WZ {k} (by omega)
  _ = (G {n} ({n}{num2}) - G {n} 0) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    congr 3
    apply sum_range_sub"""
,
"simp [G, F]",
    "field_simp [ne_zeroB {n}, ne_zeroB_succ {n}, ne_zeroB' {n}]",
    "simp [mul_comm (B {n})]",
    "rw [add_sub_right_comm, ← sub_mul, add_assoc, ← add_mul]",
    "nth_rw 1 [show B ({n} + 1) = (B ({n} + 1) / B {n}) * B {n} by field_simp [ne_zeroB]]",
    "conv_lhs => enter[1];rw[← mul_assoc]",
    "rw [← add_mul]",
    "simp only [_root_.mul_eq_zero]",
    "left",
    "rw [sub_right_comm,← sub_one_mul,aux₃ {n}, aux₄ {n}, aux₅ {n}]",
    "simp only [A, R]",
    "field_simp"
]
FIXED_CALC_TACTIC_LIST_WITH_PRIMISE = ["intro {n} primise",
"have WZ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → F ({n} + 1) {k} - F {n} {k} = G {n} ({k} + 1) - G {n} {k} := by sorry",
"""
calc f ({n} + 1) - f {n}
  _ = (∑ {k} ∈ range ({n}{num1}), (F ({n} + 1) {k} - F {n} {k})) + F ({n} + 1) ({n}{num1}) := by
    simp [f]
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
  _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    {calc_rw}
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
    congr 2
    apply Finset.sum_congr rfl
    intro {k} hidx
    simp only [mem_range] at hidx
    exact WZ {n} {k} (by omega)
  _ = (G {n} ({n}{num2}) - G {n} 0) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    congr 3
    apply sum_range_sub"""
,
"simp [G, F]",
    "field_simp [ne_zeroB {n} (by omega), ne_zeroB_succ {n} (by omega), ne_zeroB' {n} (by omega)]",
    "simp [mul_comm (B {n})]",
    "rw [add_sub_right_comm, ← sub_mul, add_assoc, ← add_mul]",
    "nth_rw 1 [show B ({n} + 1) = (B ({n} + 1) / B {n}) * B {n} by field_simp [ne_zeroB {n} (by omega)]]",
    "conv_lhs => enter[1];rw[← mul_assoc]",
    "rw [← add_mul]",
    "simp only [_root_.mul_eq_zero]",
    "left",
    "rw [sub_right_comm,← sub_one_mul,aux₃ {n} (by omega), aux₄ {n} (by omega), aux₅ {n} (by omega)]",
    "simp only [A, R]",
    "field_simp"
]

FIXED_CALC_TACTIC_LIST_Bn0 = ["intro {n}",
"have WZ ({k} : ℕ) (htotalNumidx:{k} < {n}) : F ({n} + 1) {k} - F {n} {k} = G {n} ({k} + 1) - G {n} {k} := by sorry",
"""
calc f ({n} + 1) - f {n}
  _ = (∑ {k} ∈ range ({n}{num1}), (F ({n} + 1) {k} - F {n} {k})) + F ({n} + 1) ({n}{num1}) := by
    simp [f]
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
  _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    {calc_rw}
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
    congr 2
    apply Finset.sum_congr rfl
    intro {k} hidx
    simp only [mem_range] at hidx
    exact WZ {k} (by omega)
  _ = (G {n} ({n}{num2}) - G {n} 0) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
    congr 3
    apply sum_range_sub"""
,
"simp [G, R]","rw [aux₃ {n}, aux₄ {n}]"
]
FIXED_CALC_TACTIC_LIST_WITH_PRIMISE_Bn0 = ["intro {n} primise",
"have WZ : ∀ {n} {k} : ℕ, {n} > {k} ∧ {primise} → A ({n} + 1) {k} - A {n} {k} = G {n} ({k} + 1) - G {n} {k} := by sorry",
"""
calc f ({n} + 1) - f {n}
  _ = (∑ {k} ∈ range ({n}{num1}), (A ({n} + 1) {k} - A {n} {k})) + A ({n} + 1) ({n}{num1}) := by
    simp [f]
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
  _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
    {calc_rw}
    rw [Finset.sum_range_add]
    simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
    congr 2
    apply Finset.sum_congr rfl
    intro {k} hidx
    simp only [mem_range] at hidx
    exact WZ {n} {k} (by omega)
  _ = (G {n} ({n}{num2}) - G {n} 0) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
    congr 3
    apply sum_range_sub"""
,
"simp [G, R]","rw [aux₃ {n} (by omega), aux₄ {n} (by omega)]"
]

FIXED_CALC  = \
"""
    calc f ({n} + 1) - f {n}
      _ = (∑ {k} ∈ range ({n}{num1}), (F ({n} + 1) {k} - F {n} {k})) + F ({n} + 1) ({n}{num1}) := by
        simp [f]
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
      _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
        {calc_rw}
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
        congr 2
        apply Finset.sum_congr rfl
        intro {k} hidx
        simp only [mem_range] at hidx
        exact WZ {k} (by omega)
      _ = (G {n} ({n}{num2}) - G {n} 0) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
        congr 3
        apply sum_range_sub

    simp [G, F]
    field_simp [ne_zeroB {n}, ne_zeroB_succ {n}, ne_zeroB' {n}]
    simp [mul_comm (B {n})]
    rw [add_sub_right_comm, ← sub_mul, add_assoc, ← add_mul]
    nth_rw 1 [show B ({n} + 1) = (B ({n} + 1) / B {n}) * B {n} by field_simp [ne_zeroB]]
    conv_lhs => enter[1];rw[← mul_assoc]
    rw [← add_mul]
    simp only [_root_.mul_eq_zero]
    left
    rw [sub_right_comm,← sub_one_mul,aux₃ {n}, aux₄ {n}, aux₅ {n}]
    simp only [A, R]
    field_simp
"""
FIXED_CALC_WITH_PRIMISE  = \
"""
    calc f ({n} + 1) - f {n}
      _ = (∑ {k} ∈ range ({n}{num1}), (F ({n} + 1) {k} - F {n} {k})) + F ({n} + 1) ({n}{num1}) := by
        simp [f]
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
      _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
        {calc_rw}
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
        congr 2
        apply Finset.sum_congr rfl
        intro {k} hidx
        simp only [mem_range] at hidx
        exact WZ {n} {k} (by omega)
      _ = (G {n} ({n}{num2}) - G {n} 0) + F ({n} + 1) ({n}{num2}) - F {n} ({n}{num2}) + F ({n} + 1) ({n}{num1}) := by
        congr 3
        apply sum_range_sub

    simp [G, F]
    field_simp [ne_zeroB {n} (by omega), ne_zeroB_succ {n} (by omega), ne_zeroB' {n} (by omega)]
    simp [mul_comm (B {n})]
    rw [add_sub_right_comm, ← sub_mul, add_assoc, ← add_mul]
    nth_rw 1 [show B ({n} + 1) = (B ({n} + 1) / B {n}) * B {n} by field_simp [ne_zeroB]]
    conv_lhs => enter[1];rw[← mul_assoc]
    rw [← add_mul]
    simp only [_root_.mul_eq_zero]
    left
    rw [sub_right_comm,← sub_one_mul,aux₃ {n} (by omega), aux₄ {n} (by omega), aux₅ {n} (by omega)]
    simp only [A, R]
    field_simp
"""
FIXED_CALC_Bn0  = \
"""
    calc f ({n} + 1) - f {n}
      _ = (∑ {k} ∈ range ({n}{num1}), (A ({n} + 1) {k} - A {n} {k})) + A ({n} + 1) ({n}{num1}) := by
        simp [f]
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
      _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
        {calc_rw}
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
        congr 2
        apply Finset.sum_congr rfl
        intro {k} hidx
        simp only [mem_range] at hidx
        exact WZ {k} (by omega)
      _ = (G {n} ({n}{num2}) - G {n} 0) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
        congr 3
        apply sum_range_sub
    simp [G, R]
    rw [aux₃ {n}, aux₄ {n}]

"""
FIXED_CALC_WITH_PRIMISE_Bn0  = \
"""
    calc f ({n} + 1) - f {n}
      _ = (∑ {k} ∈ range ({n}{num1}), (A ({n} + 1) {k} - A {n} {k})) + A ({n} + 1) ({n}{num1}) := by
        simp [f]
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, sub_add_eq_add_sub]
      _ = (∑ {k} ∈ range ({n}{num2}), (G {n} ({k} + 1) - G {n} {k})) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
        {calc_rw}
        rw [Finset.sum_range_add]
        simp only [range_one, sum_singleton, add_zero, add_left_inj, add_sub]
        congr 2
        apply Finset.sum_congr rfl
        intro {k} hidx
        simp only [mem_range] at hidx
        exact WZ {n} {k} (by omega)
      _ = (G {n} ({n}{num2}) - G {n} 0) + A ({n} + 1) ({n}{num2}) - A {n} ({n}{num2}) + A ({n} + 1) ({n}{num1}) := by
        congr 3
        apply sum_range_sub

    simp [G, R]
    rw [aux₃ {n} (by omega), aux₄ {n} (by omega)]
"""
DEF_PREFIX = \
"""
  let A : ℕ → ℕ → ℝ := fun (n k : ℕ) => {Ank}
  let B : ℕ → ℝ := fun n : ℕ => {Bn}
  let F : ℕ → ℕ → ℝ := fun n k => (A n k / B n)
  let f : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n{num1}), F n k
  let R : ℕ → ℕ → ℝ := fun n k => {cert}
  let G : ℕ → ℕ → ℝ:= fun (n k : ℕ) => R n k * F n k
"""