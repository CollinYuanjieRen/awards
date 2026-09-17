/-
Comparator-style challenge module for JSP-000669 / Erdős Problem #812 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
the `Proof` library (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos812Challenge

/-- The colouring `G` (red = edges) is `(m, n)`-good: no red `K_m` and no blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop := G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every colouring of `K_N` has a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The Ramsey number `r(m, n)`: the least `N` with `RamseyProp N m n`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

theorem R_succ_ge_all (n : ℕ) : R n + (4 * n - 4) ≤ R (n + 1) := by
  sorry

theorem R_succ_sub_ge : ∀ n : ℕ, 2 ≤ n → (R (n + 1) : ℤ) - (R n : ℤ) ≥ 4 * (n : ℤ) - 8 := by
  sorry

theorem ramsey_succ_right (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ramsey m n + (2 * m - 3) ≤ ramsey m (n + 1) := by
  sorry

theorem ramseyProp_ramsey (m n : ℕ) : RamseyProp (ramsey m n) m n := by
  sorry

end Erdos812Challenge
