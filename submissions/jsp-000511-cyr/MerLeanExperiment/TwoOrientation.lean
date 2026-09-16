/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Prod

open Finset
open scoped SimpleGraph
namespace PlanarListColoring
universe u
variable {V : Type u}
noncomputable local instance decidableEqForTwoOrientation : DecidableEq V := Classical.decEq V

/-- An orientation represented by its chosen tail endpoint.  The auxiliary
slot is the Hall matching certificate: injectivity of `(tail, slot)` implies
that no vertex is the tail of more than two edges. -/
structure TwoOrientation (G : SimpleGraph V) where
  tail : G.edgeSet → V
  slot : G.edgeSet → Fin 2
  tail_mem (e : G.edgeSet) : tail e ∈ e.1.toFinset
  slot_injective : Function.Injective fun e => (tail e, slot e)

namespace TwoOrientation

variable {G : SimpleGraph V} (O : TwoOrientation G)

/-- The directed arc relation induced by a chosen tail for every edge. -/
def Arc (u v : V) : Prop :=
  ∃ e : G.edgeSet, O.tail e = u ∧ e.1 = s(u, v)

lemma arc_adj {u v : V} (h : O.Arc u v) : G.Adj u v := by
  obtain ⟨e, -, he⟩ := h
  change s(u, v) ∈ G.edgeSet
  exact he ▸ e.2

lemma arc_ne {u v : V} (h : O.Arc u v) : u ≠ v :=
  (O.arc_adj h).ne

lemma arc_or_arc_symm {u v : V} (h : G.Adj u v) : O.Arc u v ∨ O.Arc v u := by
  classical
  let e : G.edgeSet := ⟨s(u, v), h⟩
  have ht := O.tail_mem e
  change O.tail e ∈ s(u, v).toFinset at ht
  rw [Sym2.mem_toFinset, Sym2.mem_iff] at ht
  rcases ht with ht | ht
  · exact Or.inl ⟨e, ht, rfl⟩
  · exact Or.inr ⟨e, ht, Sym2.eq_swap⟩

/-- The canonically represented edge underlying an arc. -/
def edgeOfArc {u v : V} (h : O.Arc u v) : G.edgeSet :=
  ⟨s(u, v), O.arc_adj h⟩

@[simp]
lemma edgeOfArc_val {u v : V} (h : O.Arc u v) : (O.edgeOfArc h).1 = s(u, v) := rfl

lemma tail_edgeOfArc {u v : V} (h : O.Arc u v) : O.tail (O.edgeOfArc h) = u := by
  rcases h with ⟨e, he, hval⟩
  have heq : O.edgeOfArc ⟨e, he, hval⟩ = e := Subtype.ext hval.symm
  rw [heq]
  exact he

/-- Out-neighbours inside a finite active vertex set. -/
noncomputable def outNeighbors (U : Finset V) (v : V) : Finset V :=
  by
    classical
    exact U.filter (O.Arc v)

@[simp]
lemma mem_outNeighbors {U : Finset V} {v w : V} :
    w ∈ O.outNeighbors U v ↔ w ∈ U ∧ O.Arc v w := by
  simp [outNeighbors]

lemma outNeighbors_mono {U W : Finset V} (hUW : U ⊆ W) (v : V) :
    O.outNeighbors U v ⊆ O.outNeighbors W v := by
  intro w hw
  simp only [mem_outNeighbors] at hw ⊢
  exact ⟨hUW hw.1, hw.2⟩

/-- The Hall slots force outdegree at most two, also after restriction to any
finite active vertex set. -/
lemma card_outNeighbors_le_two (U : Finset V) (v : V) :
    (O.outNeighbors U v).card ≤ 2 := by
  let f : {w // w ∈ O.outNeighbors U v} → Fin 2 := fun w =>
    O.slot (O.edgeOfArc ((O.mem_outNeighbors.mp w.2).2))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxarc := (O.mem_outNeighbors.mp x.2).2
    have hyarc := (O.mem_outNeighbors.mp y.2).2
    have hpair :
        (O.tail (O.edgeOfArc hxarc), O.slot (O.edgeOfArc hxarc)) =
          (O.tail (O.edgeOfArc hyarc), O.slot (O.edgeOfArc hyarc)) := by
      rw [O.tail_edgeOfArc hxarc, O.tail_edgeOfArc hyarc]
      exact Prod.ext rfl hxy
    have hedge := O.slot_injective hpair
    have hsym : s(v, x.1) = s(v, y.1) := congrArg Subtype.val hedge
    rw [Sym2.eq_iff] at hsym
    rcases hsym with h | h
    · exact h.2
    · exact (O.arc_ne hxarc h.2.symm).elim
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe (O.outNeighbors U v)]
  exact hcard

end TwoOrientation

end PlanarListColoring
