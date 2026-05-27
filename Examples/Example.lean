import Mathlib
import WZProver

open Real Nat Finset BigOperators Polynomial

set_option maxHeartbeats 8000000000

theorem Jihuai_E1_1 (n : ℕ) :  ∑ k ∈ Finset.range (n + 1), 2^k * n.choose k = 3^n := by
  --wz_prove
  sorry
