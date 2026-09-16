import Mathlib

/-!
# Erdős Problem 902 (Schütte's tournament problem): definitions

A *tournament* on a type `V` is a relation `r` (read `r u v` as "`u` beats `v`") that is irreflexive
and, for distinct vertices, holds in exactly one direction.  A set `S` of vertices is *dominated*
by a vertex `w` when `w ∉ S` and `w` beats every member of `S`.  The tournament has the
*`n`-domination property* when it has at least `n` vertices and every set of `n` vertices is
dominated by some vertex outside it (without the first clause a tournament on fewer than `n`
vertices would satisfy the condition vacuously and Schütte's function would be `0`).
Schütte's function `f n` is the least number of vertices of a tournament with the `n`-domination
property (as an infimum in `ℕ`, it is `0` when no such tournament exists).
-/

namespace Erdos902

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

theorem IsTournament.irrefl {V : Type*} {r : V → V → Prop} (h : IsTournament r) (v : V) :
    ¬ r v v := h.1 v

theorem IsTournament.total {V : Type*} {r : V → V → Prop} (h : IsTournament r) {u v : V}
    (huv : u ≠ v) : r u v ∨ r v u := by
  rcases h.2 u v huv with h'
  by_cases huv' : r u v
  · exact Or.inl huv'
  · exact Or.inr (by tauto)

theorem IsTournament.asymm {V : Type*} {r : V → V → Prop} (h : IsTournament r) {u v : V}
    (huv : r u v) : ¬ r v u := by
  by_cases hne : u = v
  · subst hne
    exact fun _ => h.1 u huv
  · exact (h.2 u v hne).1 huv

theorem IsTournament.ne_of_rel {V : Type*} {r : V → V → Prop} (h : IsTournament r) {u v : V}
    (huv : r u v) : u ≠ v := by
  rintro rfl
  exact h.1 _ huv

/-- The property for `n` transports along an equivalence of vertex types. -/
theorem hasProperty_of_equiv {V W : Type*} (e : V ≃ W) (r : V → V → Prop) (n : ℕ)
    (hr : HasProperty r n) : HasProperty (fun a b => r (e.symm a) (e.symm b)) n := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS⟩ := hr.1
    exact ⟨S.map e.toEmbedding, by simpa using hS⟩
  · intro S hS
    obtain ⟨w, hw1, hw2⟩ := hr.2 (S.map e.symm.toEmbedding) (by simpa using hS)
    refine ⟨e w, fun hmem => hw1 (by simpa using Finset.mem_map_of_mem e.symm.toEmbedding hmem),
      fun v hv => ?_⟩
    simpa using hw2 _ (Finset.mem_map_of_mem e.symm.toEmbedding hv)

theorem isTournament_of_equiv {V W : Type*} (e : V ≃ W) (r : V → V → Prop)
    (hr : IsTournament r) : IsTournament (fun a b => r (e.symm a) (e.symm b)) := by
  exact ⟨fun a => hr.1 _, fun a b hab => hr.2 _ _ (fun h => hab (e.symm.injective h))⟩

/-- The non-vacuity clause of `HasProperty` is automatic once the tournament has at least `n`
vertices: on such a vertex set the `n`-domination property is exactly the domination condition. -/
theorem hasProperty_iff_of_le {V : Type*} [Fintype V] {r : V → V → Prop} {n : ℕ}
    (h : n ≤ Fintype.card V) :
    HasProperty r n ↔ ∀ S : Finset V, S.card = n → ∃ w, Dominates r w S := by
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (by simpa using h)
  exact ⟨S, hS⟩

end Erdos902
