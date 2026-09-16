/-
Comparator-style challenge module for JSP-000510 / Erdős Problem #629 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Main.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos629Challenge

/-- A list assignment `L` admits a proper colouring from the lists. -/
def ListColorable {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` is `k`-choosable: every assignment of lists of size `k` admits a proper list colouring. -/
def Choosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ListColorable G L

/-- `n(k)`: the least number of vertices of a bipartite graph that is not `k`-choosable. -/
noncomputable def listThreshold (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ ¬ Choosable G k}

theorem two_pow_le_listThreshold (k : ℕ) : 2 ^ k ≤ listThreshold k := by
  sorry

theorem ert_lower_bound : ∀ k, 1 ≤ k → 2 ^ (k - 1) < listThreshold k := by
  sorry

theorem listThreshold_le : ∀ k, listThreshold k ≤ 2 * (2 * k - 1).choose k := by
  sorry

theorem listThreshold_one : listThreshold 1 = 2 := by
  sorry

end Erdos629Challenge
