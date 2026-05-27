# WZ-LLM

Generates Wilf-Zeilberger (WZ) proof sketches and lemma obligations for Lean 4 / Mathlib combinatorial identities.

Given a theorem in Lean 4 formal statement format, the prover:
1. Computes a WZ certificate via SageMath
2. Constructs a proof sketch (`.lean` file with `sorry`-filled sub-goals)
3. Extracts each sub-goal as a standalone lemma obligation (`.jsonl` file)

---

## Requirements

- **OS:** Linux x86-64 (the bundled `repl_v4.25` binary is Linux-only)
- **Git LFS:** required to clone the `repl_v4.25` binary (201 MB)
- **Conda / Miniconda:** for Python + SageMath environment
- **elan:** Lean version manager

---

## Step 1 — Clone (with Git LFS)

```bash
# Install git-lfs if not already installed
sudo apt-get install git-lfs   # Debian/Ubuntu

git lfs install
git clone https://github.com/BeibeiX0/WZ-LLM_test.git
cd WZ-LLM_test

# Make the REPL binary executable
chmod +x wz_llm/utils/lean4Kit/repl_v4.25
```

> If you cloned without git-lfs, `repl_v4.25` will be a 134-byte pointer file.
> Run `git lfs pull` to fetch the real binary.

---

## Step 2 — Python environment (SageMath + Flask)

Install [Miniconda](https://docs.conda.io/en/latest/miniconda.html) if you don't have it, then:

```bash
# Create the environment (Python 3.10, SageMath 10.5, Singular 4.4.0)
conda env create -f environment.yml

# Activate
conda activate wz_prover
```

> `environment.yml` already includes Flask and requests via pip.
> SageMath requires `singular` on PATH — the conda environment handles this automatically.
> Always run with `wz_prover` active.

---

## Step 3 — Lean 4 + Mathlib

**Lean toolchain:** `leanprover/lean4:v4.25.0`
**Mathlib:** `v4.25.0` (pinned in `lake-manifest.json`)

Install `elan` (Lean version manager) if you don't have it:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile   # or restart your shell
```

Then build Mathlib from the **repository root** (the directory containing `lakefile.toml`):

```bash
cd /path/to/WZ-LLM_test      # must be the repo root
lake exe cache get            # download pre-built Mathlib .olean files (~5 GB)
lake build                    # build the WZProver Lean library
```

> If `lake exe cache get` fails, run `lake build` directly — it compiles Mathlib from source (1–2 hours).

---

## Step 4 — Run

**All commands must be run from the repository root (`WZ-LLM_test/`)**, because `lake env` needs `lakefile.toml` in the current directory.

### Batch mode

```bash
cd /path/to/WZ-LLM_test
conda activate wz_prover

python wz_llm/run_batch.py \
    --input wz_llm/test_set/LCI_test.jsonl \
    --output-dir output/run1

# Run in background:
nohup python wz_llm/run_batch.py \
    --input wz_llm/test_set/LCI_test.jsonl \
    --output-dir output/run1 > run.log 2>&1 &
```

**Input JSONL format** (one theorem per line):
```json
{"name": "theorem_name", "formal_statement": "theorem theorem_name (n : ℕ) : ... := by\n  sorry"}
```

### HTTP server mode

```bash
cd /path/to/WZ-LLM_test
conda activate wz_prover
python wz_llm/server.py
```

POST to `http://localhost:5001/parse`:
```bash
curl -X POST http://localhost:5001/parse \
     -H "Content-Type: application/json" \
     -d '{"theorem": "theorem idt (n : ℕ) : ∑ k in Finset.range (n+1), Nat.choose n k = 2^n := by\n  sorry"}'
```

---

## Output format

**Sketch** (`output/run1/sketches/<name>.lean`): a complete Lean 4 proof with `sorry` placeholders for each sub-goal.

**Lemmas** (`output/run1/lemmas/<name>.jsonl`): one lemma per line, each a self-contained Lean 4 theorem statement:

```json
{"formal_statement": "theorem hwz (n : ℕ) (hn : n ≥ 1) : (2 * ↑n + 1 : ℝ) ≠ 0 := by\n  sorry", "type": "hwz"}
```

Lemma types:
- `hwz` — non-zero side conditions required during the WZ proof
- `rwz` — ratio/recurrence identities
- `case_pos` — base case obligations (e.g. `n = 0`)

---

## Directory structure

```
WZ-LLM_test/                         ← lake project root (run all commands from here)
├── lakefile.toml                     # Lean project config (depends on Mathlib v4.25.0)
├── lean-toolchain                    # leanprover/lean4:v4.25.0
├── lake-manifest.json                # pinned dependency versions
├── WZProver/                         # Lean 4 WZ tactic source
│   └── Tactic/WZProve.lean
├── environment.yml                   # conda environment spec
├── requirements.txt                  # pip packages (Flask, requests)
└── wz_llm/                           # Python prover code
    ├── run_batch.py                  # batch entry point
    ├── server.py                     # Flask HTTP server
    ├── test_set/
    │   └── LCI_test.jsonl            # 100-theorem test set
    └── utils/
        ├── WZProver.py               # core WZ prover logic
        ├── Constant.py               # config (timeouts, REPL version, import header)
        ├── Sage.py                   # SageMath WZ certificate computation
        ├── Sage_Python.py            # Python-side Sage helpers
        ├── lean2sage.py              # Lean expression → Sage translator
        ├── lean2maple.py             # Lean expression → Maple translator
        ├── strip_even_power.py
        └── lean4Kit/
            ├── Lean4Kit.py           # Python wrapper for the Lean 4 REPL
            ├── LeanKitException.py
            └── repl_v4.25            # Lean 4 REPL binary (Linux x86-64, stored via Git LFS)
```

---

## Troubleshooting

| Error | Cause | Fix |
|-------|-------|-----|
| `repl_v4.25` is 134 bytes | Cloned without git-lfs | `git lfs pull` |
| `Permission denied: repl_v4.25` | Binary not executable | `chmod +x wz_llm/utils/lean4Kit/repl_v4.25` |
| `lake: command not found` | elan/Lean not installed | Install elan, then `lake build` |
| `error: no such file or directory: lakefile.toml` | Not running from repo root | `cd /path/to/WZ-LLM_test` first |
| `singular is not available` | Singular not on PATH | `conda activate wz_prover` |
| `No module named 'sage'` | Wrong Python interpreter | `conda activate wz_prover` |
| `invalid syntax (<string>, line 1)` | Sage cannot parse the theorem | Theorem uses non-polynomial terms outside WZ scope |
| `divide: arguments must be polynomials` | WZ method not applicable | Theorem is not a hypergeometric identity |
