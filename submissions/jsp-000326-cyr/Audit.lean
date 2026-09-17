import Erdos396Catalan

#print axioms erdos_396_remark
#print axioms erdos_396_catalan_eq_div

/-- Erdős #396: `n + 1 ∣ C(2n, n)` and `C(2n, n) = (n + 1) · catalan n`. -/
example (n : ℕ) : n + 1 ∣ (2 * n).choose n ∧ (2 * n).choose n = (n + 1) * catalan n :=
  erdos_396_remark n
