/-
Comparator-style challenge module for JSP-000094 / Erdős Problem #77 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Limit` with `sorry`, so the statements can be compared mechanically with those proved in
the `Proof` library (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos77Challenge

/-- The colouring `G` (red = edges) is `(m, n)`-good: no red `K_m` and no blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every colouring of `K_N` has a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The Ramsey number `r(m, n)`: the least `N` with `RamseyProp N m n`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

theorem sqrt_two_le_liminf :
    Real.sqrt 2 ≤ Filter.liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop := by
  sorry

theorem limsup_le_four : Filter.limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop ≤ 4 := by
  sorry

theorem sqrt_two_le_R_rpow (k : ℕ) (hk : 3 ≤ k) : Real.sqrt 2 ≤ (R k : ℝ) ^ (1 / (k : ℝ)) := by
  sorry

theorem R_rpow_le_four (k : ℕ) (hk : 1 ≤ k) : (R k : ℝ) ^ (1 / (k : ℝ)) ≤ 4 := by
  sorry

end Erdos77Challenge
