/-
Comparator-style challenge module for JSP-000987 / Erdős Problem #1182 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean` and `Proof/TriRamsey.lean`,
repeated verbatim). Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos1182Challenge

open SimpleGraph

/-- The colouring `G` (red = edges, blue = non-edges) is `(m, n)`-good when it contains
neither a red `K_m` nor a blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- Every red/blue colouring of `K_N` contains a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The two-colour Ramsey number `r(m, n)`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- Every red/blue colouring of `K_N` has a red triangle or a blue copy of `G`. -/
def TriRamseyProp (N : ℕ) {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph (Fin N), ¬ R.CliqueFree 3 ∨ G ⊑ Rᶜ

/-- `R(K_3, G)`: the least `N` with `TriRamseyProp N G`. -/
noncomputable def triRamsey {W : Type*} (G : SimpleGraph W) : ℕ := sInf {N : ℕ | TriRamseyProp N G}

/-- The page's trivial bound for connected graphs on `n` vertices. -/
def ConnLowerBound (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.Connected → 2 * n - 1 ≤ triRamsey G

theorem not_exists_connected_triRamsey_lt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), G.Connected ∧ triRamsey G < 2 * n - 1 := by
  sorry

theorem connLowerBound (n : ℕ) : ConnLowerBound n := by
  sorry

theorem le_triRamsey_of_connected (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    2 * n - 1 ≤ triRamsey G := by
  sorry

theorem not_triRamseyProp_of_connected (n N : ℕ) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hN : N ≤ 2 * n - 2) : ¬ TriRamseyProp N G := by
  sorry

theorem triRamseyProp_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : TriRamseyProp (ramsey 3 n) G := by
  sorry

theorem triRamsey_le_ramsey (n : ℕ) (G : SimpleGraph (Fin n)) : triRamsey G ≤ ramsey 3 n := by
  sorry

end Erdos1182Challenge
