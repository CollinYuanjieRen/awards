import Mathlib

/-!
# Erdős Problem #396: `n + 1` always divides `C(2n, n)` (Catalan numbers)

Erdős and Graham asked whether for every `k` there is `n` with `∏_{0 ≤ i ≤ k} (n − i) ∣ C(2n, n)`
(OPEN; not addressed here, nor Pomerance's density results).  The problem page records: "Erdős
and Graham write that `n + 1` always divides `C(2n, n)` (indeed `C(2n, n)/(n + 1)` is the `n`th
Catalan number), but it is quite rare that `n` divides `C(2n, n)`."  This file proves the first
two claims for every `n`, in the page's binomial-coefficient form: `n + 1 ∣ C(2n, n)` and
`C(2n, n) = (n + 1) · catalan n` with Mathlib's Catalan numbers; the (informal) rarity remark
and the main question are not claimed.  The statement is ours (the formal-conjectures rendering
`Erdos396.erdos_396` uses `Nat.centralBinom n = C(2n, n)` for the main question).  Disclosure:
both facts are already Mathlib theorems (`Nat.succ_dvd_centralBinom`,
`succ_mul_catalan_eq_centralBinom`, `catalan_eq_centralBinom_div`); this file only restates them
in the page's binomial form, and claims no new mathematics.
-/

/-- **Erdős #396, the page's remark**: `n + 1 ∣ C(2n, n)`, and `C(2n, n) = (n + 1) · catalan n`. -/
theorem erdos_396_remark (n : ℕ) :
    n + 1 ∣ (2 * n).choose n ∧ (2 * n).choose n = (n + 1) * catalan n := by
  refine ⟨?_, ?_⟩
  · rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.succ_dvd_centralBinom n
  · rw [← Nat.centralBinom_eq_two_mul_choose, succ_mul_catalan_eq_centralBinom]

/-- The quotient `C(2n, n)/(n + 1)` is the `n`th Catalan number. -/
theorem erdos_396_catalan_eq_div (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  exact catalan_eq_centralBinom_div n
