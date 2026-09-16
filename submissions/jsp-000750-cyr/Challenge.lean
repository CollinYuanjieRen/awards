/-
Comparator-style challenge module for JSP-000750 / Erdős Problem #902 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of `Proof.Main` with `sorry`, so the statements can be compared mechanically with those proved in
`Proof/Main.lean` (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos902Challenge

/-- `r` is a tournament: irreflexive, and for `u ≠ v` exactly one of `r u v`, `r v u` holds. -/
def IsTournament {V : Type*} (r : V → V → Prop) : Prop :=
  (∀ v, ¬ r v v) ∧ ∀ u v, u ≠ v → (r u v ↔ ¬ r v u)

/-- `w` dominates the vertex set `S`: `w ∉ S` and `w` beats every vertex of `S`. -/
def Dominates {V : Type*} (r : V → V → Prop) (w : V) (S : Finset V) : Prop :=
  w ∉ S ∧ ∀ v ∈ S, r w v

/-- The `n`-domination property: there is at least one set of `n` vertices (so the condition is
not vacuous), and every set of `n` vertices is dominated by some vertex outside it. -/
def HasProperty {V : Type*} (r : V → V → Prop) (n : ℕ) : Prop :=
  (∃ S : Finset V, S.card = n) ∧ ∀ S : Finset V, S.card = n → ∃ w, Dominates r w S

/-- Schütte's function: the least number of vertices of a tournament in which every set of `n`
vertices is dominated by an outside vertex. -/
noncomputable def schutte (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n}

theorem two_pow_sub_one_le_of_hasProperty (N n : ℕ) (r : Fin N → Fin N → Prop)
    (hr : IsTournament r) (hn : HasProperty r n) : 2 ^ (n + 1) - 1 ≤ N := by
  sorry

theorem two_pow_sub_one_le_schutte (n : ℕ)
    (h : ∃ N : ℕ, ∃ r : Fin N → Fin N → Prop, IsTournament r ∧ HasProperty r n) :
    2 ^ (n + 1) - 1 ≤ schutte n := by
  sorry

theorem schutte_one : schutte 1 = 3 := by
  sorry

theorem schutte_two : schutte 2 = 7 := by
  sorry

end Erdos902Challenge
