/-
Comparator-style challenge module for JSP-000855 / Erdős Problem #1029 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Lower` and `Proof.Sharp` with `sorry`, so the statements can be compared mechanically
with those proved in the `Proof` library (the definitions below are the ones of `Proof/Defs.lean`,
repeated verbatim). Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos1029Challenge

/-- The colouring `G` (red = edges) is `(m, n)`-good: no red `K_m` and no blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every colouring of `K_N` has a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The Ramsey number `r(m, n)`: the least `N` with `RamseyProp N m n`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

theorem mul_two_pow_half_le (k : ℕ) :
    (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * Real.sqrt 2 * Real.exp 1 * ((R k : ℝ) + 1) := by
  sorry

theorem two_pow_lt_R_sq (k : ℕ) (hk : 3 ≤ k) : 2 ^ k < R k ^ 2 := by
  sorry

theorem ramsey_le_choose_sharp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ramsey m n ≤ (m + n - 2).choose (m - 1) := by
  sorry

theorem R_le_choose_page (k : ℕ) (hk : 1 ≤ k) : R k ≤ (2 * k - 1).choose (k - 1) := by
  sorry

theorem lt_R_of_count (k N : ℕ) (hkN : k ≤ N)
    (h : N.choose k * 2 * 2 ^ (N.choose 2 - k.choose 2) < 2 ^ (N.choose 2)) : N < R k := by
  sorry

end Erdos1029Challenge
