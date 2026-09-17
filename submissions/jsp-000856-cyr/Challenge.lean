/-
Comparator-style challenge module for JSP-000856 / Erdős Problem #1030 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.OffDiagonal` with `sorry`, so the statements can be compared mechanically with those
proved in the `Proof` library (the definitions below are the ones of `Proof/Defs.lean`, repeated
verbatim). Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos1030Challenge

/-- The colouring `G` (red = edges) is `(m, n)`-good: no red `K_m` and no blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every colouring of `K_N` has a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The Ramsey number `r(m, n)`: the least `N` with `RamseyProp N m n`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

theorem offdiag_sub_ge (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ 2 * (k : ℤ) - 5 := by
  sorry

theorem offdiag_ge (k : ℕ) (hk : 2 ≤ k) : R k + (2 * k - 3) ≤ ramsey (k + 1) k := by
  sorry

theorem offdiag_sub_ge_trivial (k : ℕ) : (ramsey (k + 1) k : ℤ) - (R k : ℤ) ≥ (k : ℤ) - 2 := by
  sorry

end Erdos1030Challenge
