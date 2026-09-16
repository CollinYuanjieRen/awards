/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/
import MerLeanExperiment.TwoOrientation
import Mathlib.Combinatorics.Hall.Basic

open Finset
open scoped SimpleGraph
namespace PlanarListColoring
universe u
variable {V : Type u}
noncomputable local instance decidableEqForHallOrientation : DecidableEq V := Classical.decEq V

/-! ## Hall--Hakimi orientation -/

/-- The endpoint slots available to an edge. -/
noncomputable def edgeSlots {G : SimpleGraph V} (e : G.edgeSet) : Finset (V × Fin 2) :=
  by
    classical
    exact e.1.toFinset ×ˢ Finset.univ

lemma biUnion_edgeSlots {G : SimpleGraph V} (F : Finset G.edgeSet) :
    F.biUnion edgeSlots =
      (F.biUnion fun e => e.1.toFinset) ×ˢ (Finset.univ : Finset (Fin 2)) := by
  classical
  ext x
  simp [edgeSlots]

/-- The hereditary endpoint bound gives an orientation of maximum outdegree two. -/
noncomputable def twoOrientation_of_density {G : SimpleGraph V}
    (hdensity : ∀ F : Finset G.edgeSet,
      F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card) : TwoOrientation G := by
  classical
  have hall : ∀ F : Finset G.edgeSet,
      F.card ≤ (F.biUnion edgeSlots).card := by
    intro F
    rw [biUnion_edgeSlots, Finset.card_product]
    simpa [Fintype.card_fin, mul_comm] using
      hdensity F
  let hex := (Finset.all_card_le_biUnion_card_iff_exists_injective edgeSlots).mp hall
  let matchSlot := Classical.choose hex
  have hmatch_inj := (Classical.choose_spec hex).1
  have hmatch_mem := (Classical.choose_spec hex).2
  exact
    { tail := fun e => (matchSlot e).1
      slot := fun e => (matchSlot e).2
      tail_mem := fun e => (Finset.mem_product.mp (hmatch_mem e)).1
      slot_injective := fun _ _ h => hmatch_inj (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h)) }

end PlanarListColoring
