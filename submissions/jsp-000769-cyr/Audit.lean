import Erdos926Furedi

open SimpleGraph Filter Asymptotics

#print axioms Erdos926.erdos_926
#print axioms Erdos926.extremalNumber_Hk_le
#print axioms Erdos926.erdos_926_closed
#print axioms Erdos926.card_edgeFinset_le_of_free
#print axioms Erdos926.richGraph_cliqueFree
#print axioms Erdos926.isContained_of_rich
#print axioms Erdos926.turan_bound
#print axioms Erdos926.poorOrd_ge

/-- Erdős Problem 926: for every `k ≥ 4`, `ex(n; H_k) = O(n^{3/2})`. -/
example (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ => (extremalNumber n (Erdos926.Hk k) : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) :=
  Erdos926.erdos_926 k hk

/-- The explicit form: `ex(n; H_k) ≤ k^{3/2} n^{3/2} + k n` for every `k ≥ 2` and every `n`. -/
example (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (extremalNumber n (Erdos926.Hk k) : ℝ) ≤
      (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) + k * n :=
  Erdos926.extremalNumber_Hk_le k hk n
