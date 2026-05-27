"""Run WZProver on a JSONL test set to generate WZ proof sketches and lemma obligations.

Usage::

    cd /path/to/WZ-LLM          # must be the lake project root (contains lakefile.toml)
    conda activate wz_prover
    python wz_llm/run_batch.py \\
        --input path/to/theorems.jsonl \\
        --output-dir output/run1

    # Run in background and log output:
    nohup python wz_llm/run_batch.py --input wz_llm/test_set/LCI_test.jsonl --output-dir output/run1 > run.log 2>&1 &

The input JSONL must have one theorem per line with fields:
    {"name": "theorem_name", "formal_statement": "theorem ... := by\\n  sorry"}

Outputs per theorem (skipped if already exists):
  - output-dir/sketches/<name>.lean   — full WZ proof sketch
  - output-dir/lemmas/<name>.jsonl    — extracted lemma obligations
  - output-dir/_progress.jsonl        — checkpoint (one line per theorem)
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from utils.Constant import IMPORT_CONTENT, REPL_VERSION
from utils.lean4Kit.Lean4Kit import Lean4Kit
from utils.WZProver import WZProver

parser = argparse.ArgumentParser()
parser.add_argument("--input", required=True, help="Path to input JSONL file")
parser.add_argument("--output-dir", default="output/run", help="Directory for sketches and lemmas")
args = parser.parse_args()

INPUT_JSONL       = Path(args.input)
OUTPUT_DIR        = Path(args.output_dir)
OUTPUT_LEMMA_DIR  = OUTPUT_DIR / "lemmas"
OUTPUT_SKETCH_DIR = OUTPUT_DIR / "sketches"

OUTPUT_LEMMA_DIR.mkdir(parents=True, exist_ok=True)
OUTPUT_SKETCH_DIR.mkdir(parents=True, exist_ok=True)

# Load all problems
problems = {}
with open(INPUT_JSONL) as f:

    for line in f:
        if not line.strip():
            continue
        prob = json.loads(line)
        problems[prob["name"]] = prob["formal_statement"]

total = len(problems)
print(f"Loaded {total} theorems from {INPUT_JSONL}")

# Initialize prover once
print("Initializing Lean4Kit and WZProver...")
lean = Lean4Kit(str(HERE.parent), REPL_VERSION, verbose=False)
prover = WZProver(lean, None)
prover.set_searcher(None)
prover.init_theorem(lean, bert_sim=None, theorem_statement=None)
print("Prover ready.\n")


def count_lemmas(path):
    if not path.exists():
        return 0
    with open(path) as f:
        return sum(1 for l in f if l.strip())


results = []
t_start = time.time()

for idx, (name, formal_stmt) in enumerate(problems.items(), 1):
    lemma_file  = OUTPUT_LEMMA_DIR / f"{name}.jsonl"
    sketch_file = OUTPUT_SKETCH_DIR / f"{name}.lean"

    # Skip if already done
    if sketch_file.exists() and lemma_file.exists() and lemma_file.stat().st_size > 0:
        n = count_lemmas(lemma_file)
        print(f"[{idx:3d}/{total}] SKIP (exists) {name}  lemmas={n}")
        results.append({"name": name, "status": "skip", "lemma_count": n})
        continue

    print(f"\n[{idx:3d}/{total}] {name}")

    lemma_file.write_text("")
    prover.lemma_path = str(lemma_file)

    t0 = time.time()
    try:
        tactic = prover.prove(formal_stmt, IMPORT_CONTENT)
        elapsed = time.time() - t0
        sketch_file.write_text(f"{IMPORT_CONTENT}\n{formal_stmt}:= by\n{tactic}\n")
        status = "ok"
    except Exception as e:
        elapsed = time.time() - t0
        tactic = None
        status = f"error: {e}"

    n = count_lemmas(lemma_file)
    elapsed_total = time.time() - t_start
    print(f"  Status : {status} ({elapsed:.1f}s)  lemmas={n}  total_elapsed={elapsed_total/60:.1f}min")

    results.append({"name": name, "status": status, "lemma_count": n})

    # Flush progress to a checkpoint file after each theorem
    checkpoint = OUTPUT_LEMMA_DIR / "_progress.jsonl"
    with open(checkpoint, "a") as f:
        f.write(json.dumps({"idx": idx, "name": name, "status": status, "lemma_count": n}) + "\n")

print(f"\n{'='*60}")
print("FINAL SUMMARY")
print(f"{'='*60}")
ok      = [r for r in results if r["status"] == "ok"]
skipped = [r for r in results if r["status"] == "skip"]
errors  = [r for r in results if r["status"] not in ("ok", "skip")]
total_lemmas = sum(r["lemma_count"] for r in results)

print(f"  ok:      {len(ok)}")
print(f"  skipped: {len(skipped)}")
print(f"  errors:  {len(errors)}")
print(f"  total lemmas extracted: {total_lemmas}")
print(f"  total time: {(time.time()-t_start)/60:.1f} min")

if errors:
    print("\nFailed theorems:")
    for r in errors:
        print(f"  {r['name']}: {r['status']}")

print(f"\nLemmas  → {OUTPUT_LEMMA_DIR}")
print(f"Sketches → {OUTPUT_SKETCH_DIR}")
