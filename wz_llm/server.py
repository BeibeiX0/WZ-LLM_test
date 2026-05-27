"""Flask server exposing the WZ prover as an HTTP API.

Usage::

    python wz_sever.py

Then POST a JSON body to ``/parse``::

    curl -X POST http://localhost:5001/parse \\
         -H "Content-Type: application/json" \\
         -d '{"theorem": "theorem idt_4 (n : ℕ) : ..."}'
"""

from flask import Flask, request, jsonify
from pathlib import Path
import time

from utils.Constant import IMPORT_CONTENT, REPL_VERSION
from utils.lean4Kit.Lean4Kit import Lean4Kit
from utils.WZProver import WZProver

# Lean project root: server.py lives inside wz_prover/
LEAN_WORK_DIR = str(Path(__file__).resolve().parent.parent)

# Create Flask application instance
app = Flask(__name__)

# Global prover instance (initialized once at startup)
prover = None

# Directory for generated lemma files used by WZProver internals
LEMMA_DIR = LEAN_WORK_DIR + "/output/api_lemmas"


def init_prover():
    """Initialize the Lean4Kit and WZProver instances."""
    global prover
    print("Initializing Lean4Kit and WZProver...")
    lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=False)
    prover = WZProver(lean, None)
    prover.set_searcher(None)
    prover.init_theorem(lean, bert_sim=None, theorem_statement=None)
    Path(LEMMA_DIR).mkdir(parents=True, exist_ok=True)
    print("Prover ready.")


# Define routes and view functions
@app.route('/parse', methods=['POST'])
def parse():
    """Accept a theorem statement and return a tactic proof.

    Request JSON::

        {"theorem": "<Lean 4 theorem statement>"}

    Response JSON::

        {"status": "success", "tactic": "<generated tactic code>"}
        {"status": "error",   "message": "<error description>"}
    """
    if prover is None:
        return jsonify({"status": "error", "message": "Prover not initialized"}), 503

    data = request.get_json(silent=True)
    if not data or "theorem" not in data:
        return jsonify({"status": "error", "message": "Missing 'theorem' field in request body"}), 400

    formal_theorem = data["theorem"]

    try:
        # WZProver writes lemma obligations to this file during generation.
        # Use per-request unique file names to avoid collisions.
        lemma_file = Path(LEMMA_DIR) / f"wz_{int(time.time() * 1000)}.jsonl"
        prover.lemma_path = str(lemma_file)
        tactic = prover.prove(formal_theorem, IMPORT_CONTENT)
        return jsonify({"status": "success", "tactic": tactic})
    except Exception as e:
        print(f"Error proving theorem: {e}")
        return jsonify({"status": "error", "message": str(e)}), 500


# Start the application
if __name__ == '__main__':
    init_prover()
    app.run(host='0.0.0.0', port=5001, debug=False)
