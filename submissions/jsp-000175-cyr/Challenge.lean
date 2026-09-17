/-
Comparator-style challenge module for JSP-000175 / Erdős Problem #181 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/RamseyDefs.lean` and `Proof/Defs.lean`,
repeated verbatim).  Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos181Challenge

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

/-- The `n`-dimensional hypercube graph `Q_n`. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v => ∃ i, u i ≠ v i ∧ ∀ j, j ≠ i → u j = v j)

/-- Every red/blue colouring of `K_N` contains a red or a blue copy of `G`. -/
def GraphRamseyProp {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph (Fin N), G ⊑ R ∨ G ⊑ Rᶜ

/-- The graph Ramsey number `R(G)`. -/
noncomputable def graphRamsey {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyProp N G}

theorem graphRamsey_hypercube_le (n : ℕ) : graphRamsey (hypercube n) ≤ 4 ^ (2 ^ n) := by
  sorry

theorem graphRamsey_hypercube_le_R (n : ℕ) : graphRamsey (hypercube n) ≤ R (2 ^ n) := by
  sorry

theorem graphRamsey_le_R {V : Type*} [Fintype V] (G : SimpleGraph V) :
    graphRamsey G ≤ R (Fintype.card V) := by
  sorry

theorem graphRamseyProp_ramsey {V : Type*} [Fintype V] (G : SimpleGraph V) :
    GraphRamseyProp (ramsey (Fintype.card V) (Fintype.card V)) G := by
  sorry

theorem isContained_of_not_cliqueFree {V : Type*} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (R : SimpleGraph (Fin N)) (hR : ¬ R.CliqueFree (Fintype.card V)) : G ⊑ R := by
  sorry

theorem ramsey_diag_le_four_pow (n : ℕ) : ramsey n n ≤ 4 ^ n := by
  sorry

end Erdos181Challenge
