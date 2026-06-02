# WZ-LLM

WZ-LLM is a Lean 4 project that provides a custom tactic:

- `wz_prove`

When you run `wz_prove` inside a theorem, Lean sends the goal to a local Python service, gets a generated WZ-style proof framework, and shows it as a clickable suggestion in Infoview (`Try this`).

---

## 1. Prerequisites

### Python

Create a Conda environment with Python and SageMath:

```bash
conda env create -f environment.yml
conda activate wz_prover
```

### Lean

Install Lean toolchain manager (`elan`) and the Lean extension in your editor (VS Code recommended).

- Elan: https://github.com/leanprover/elan
- VS Code extension: `lean4`

---

## 2. Build

```bash
cd WZ-LLM
```

Fetch dependencies and build:

```bash
lake exe cache get
lake build WZProver
```

---

## 3. Start the local WZ API server

From the project root:

```bash
conda activate wz_prover
python wz_llm/server.py
```

You should see:

- `Prover ready.`
- `Running on http://127.0.0.1:5001`

Keep this terminal running.

---

## 4. Run the example

Open:

- `Examples/Example.lean`

Example theorem:

```lean
theorem Jihuai_E1_1 (n : ℕ) : ∑ k ∈ Finset.range (n + 1), 2^k * n.choose k = 3^n := by
  wz_prove
```

How to use:

1. Put cursor on `wz_prove`
2. Wait for Infoview suggestion (`Try this` / code action)
3. Click the suggestion
4. Lean will replace `wz_prove` with the generated tactic code

Note: `wz_prove` **does not auto-apply** the tactic by itself. It provides a clickable suggestion.

---

## 5. Quick API check (optional)

If you want to verify server response directly:

```bash
curl -X POST http://127.0.0.1:5001/parse \
  -H "accept: application/json" \
  -H "Content-Type: application/json" \
  --data '{"theorem":"theorem Jihuai_E1_1 (n : ℕ) : ∑ k ∈ Finset.range (n + 1), 2^k * n.choose k = 3^n"}'
```

Expected JSON fields:

- success: `{"status":"success","tactic":"..."}`
- error: `{"status":"error","message":"..."}`

---

## 6. Troubleshooting

### `wz_prove: request failed (curl exit code 28)`

This means request timeout (not necessarily server down).

- Keep server terminal open
- Watch server logs
- Try again (some goals take longer)

### `Address already in use (port 5001)`

Another process is already using port 5001.

Find and stop it:

```bash
lsof -ti :5001
kill <PID>
```

Then restart server:

```bash
python wz_llm/server.py
```

### `No module named 'sage'` or `singular is not available`

Wrong Python environment active.

```bash
conda activate wz_prover
```

### `Server returns 'Failed to start process'`

You are likely running an old server process. Kill and restart `wz_llm/server.py` from the latest code.

---

## 7. Project structure (minimal)

- `WZProver/Tactic/WZProve.lean` — Lean tactic implementation (`wz_prove`)
- `wz_llm/server.py` — Flask API service (`/parse`)
- `wz_llm/utils/WZProver.py` — WZ framework generator backend
- `wz_llm/utils/lean4Kit/repl_v4.25` — Lean 4 REPL binary (Linux x86-64)
- `Examples/Example.lean` — beginner example

---

If you can run the server and click the Infoview suggestion in `Examples/Example.lean`, your setup is correct.
