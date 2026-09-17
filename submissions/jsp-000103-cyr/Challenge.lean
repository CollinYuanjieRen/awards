/-
Comparator-style challenge module for JSP-000103 / Erdős Problem #87 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/RamseyDefs.lean` and `Proof/Defs.lean`,
repeated verbatim).  Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos87Challenge

open SimpleGraph

/-- The colouring `G` (red = edges, blue = non-edges) is `(m, n)`-good when it contains
neither a red `K_m` nor a blue `K_n`. -/
def IsGood {V : Type*} (G : SimpleGraph V) (m n : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree n

/-- `RamseyProp N m n` says that every red/blue colouring of the complete graph on `N`
vertices contains a red `K_m` or a blue `K_n`. -/
def RamseyProp (N m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ IsGood G m n

/-- The two-colour Ramsey number `r(m, n)`. -/
noncomputable def ramsey (m n : ℕ) : ℕ := sInf {N : ℕ | RamseyProp N m n}

/-- The diagonal Ramsey number `R(n) = r(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ := ramsey n n

/-- Every red/blue colouring of `K_N` contains a red or a blue copy of `G`. -/
def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

/-- The graph Ramsey number `R(G)`. -/
noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

theorem not_exists_four_pow_mul_graphRamsey_le (n k : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), 2 ≤ k ∧ G.chromaticNumber = (k : ℕ∞) ∧
      4 ^ k * graphRamsey G ≤ R k := by
  sorry

theorem lt_graphRamsey_of_chromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) (ε : ℝ) (hε : 3 / 4 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) ^ k * (R k : ℝ) < graphRamsey G := by
  sorry

theorem R_lt_four_pow_mul_graphRamsey {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) : R k < 4 ^ k * graphRamsey G := by
  sorry

theorem two_le_graphRamsey_of_adj {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : 2 ≤ graphRamsey G := by
  sorry

theorem exists_adj_of_two_le_chromaticNumber {V : Type*} (G : SimpleGraph V)
    (h : 2 ≤ G.chromaticNumber) : ∃ u v : V, G.Adj u v := by
  sorry

theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n := by
  sorry

end Erdos87Challenge
