/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/
import MerLeanExperiment.HallOrientation
import MerLeanExperiment.KernelColoring

open Finset
open scoped SimpleGraph
namespace PlanarListColoring
universe u
variable {V : Type u}
noncomputable local instance decidableEqForColoringFromDensity : DecidableEq V := Classical.decEq V

/-- The hereditary endpoint bound implies three-list-colorability for bipartite graphs. -/
theorem three_list_colorable_of_density
    [Finite V] (G : SimpleGraph V)
    (hdensity : ∀ F : Finset G.edgeSet,
      F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card)
    (hbipartite : G.IsBipartite) (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let O : TwoOrientation G := twoOrientation_of_density hdensity
  have hkernels : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K :=
    fun X => exists_kernel_of_bipartite O hbipartite X
  have hcap : ∀ v ∈ (Finset.univ : Finset V),
      (O.outNeighbors Finset.univ v).card < (L v).card := by
    intro v _
    have hout := O.card_outNeighbors_le_two (Finset.univ : Finset V) v
    rw [hL v]
    omega
  obtain ⟨f, hfL, hfproper⟩ :=
    exists_list_coloring_on O hkernels L (Finset.univ : Finset V) hcap
  refine ⟨SimpleGraph.Coloring.mk f ?_, fun v => hfL v (Finset.mem_univ v)⟩
  intro u v huv
  exact hfproper u (Finset.mem_univ u) v (Finset.mem_univ v) huv

end PlanarListColoring
