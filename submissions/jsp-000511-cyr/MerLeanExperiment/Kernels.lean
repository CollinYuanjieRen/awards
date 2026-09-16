/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/
import MerLeanExperiment.TwoOrientation
import Mathlib.Data.Finset.Max

open Finset
open scoped SimpleGraph
namespace PlanarListColoring
universe u
variable {V : Type u}
noncomputable local instance decidableEqForKernels : DecidableEq V := Classical.decEq V

/-! ## Kernels of bipartite orientations -/

variable {G : SimpleGraph V}

/-- Vertices in the second bipartition class not yet absorbed by `S`. -/
noncomputable def residual (O : TwoOrientation G) (B S : Finset V) : Finset V :=
  by
    classical
    exact B.filter fun b => ∀ a ∈ S, ¬ O.Arc b a

/-- `S` has no arc to a second-part vertex that is not absorbed by `S`. -/
def Admissible (O : TwoOrientation G) (B S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ residual O B S, ¬ O.Arc a b

/-- A directed kernel in the subdigraph induced by `X`. -/
def IsKernel (O : TwoOrientation G) (X K : Finset V) : Prop :=
  K ⊆ X ∧
    (∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v) ∧
    ∀ v ∈ X, v ∉ K → ∃ k ∈ K, O.Arc v k

namespace IsKernel

lemma subset {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) : K ⊆ X :=
  h.1

lemma arc_free {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) : ¬ O.Arc u v :=
  h.2.1 u hu v hv

lemma absorbs {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K)
    {v : V} (hvX : v ∈ X) (hvK : v ∉ K) : ∃ k ∈ K, O.Arc v k :=
  h.2.2 v hvX hvK

lemma isIndepSet {O : TwoOrientation G} {X K : Finset V} (h : IsKernel O X K) :
    G.IsIndepSet (K : Set V) := by
  intro u hu v hv huv hadj
  rcases O.arc_or_arc_symm hadj with huv' | hvu'
  · exact h.arc_free hu hv huv'
  · exact h.arc_free hv hu hvu'

end IsKernel

/-- Every finite induced subdigraph of an orientation of a bipartite graph has
a kernel.  The proof chooses a maximum-cardinality admissible subset of one
bipartition class. -/
theorem exists_kernel_of_bipartite {G : SimpleGraph V} (O : TwoOrientation G)
    (hG : G.IsBipartite) (X : Finset V) :
    ∃ K : Finset V, IsKernel O X K := by
  classical
  rcases hG with ⟨C⟩
  let A : Finset V := X.filter fun v => C v = 0
  let B : Finset V := X.filter fun v => C v = 1
  have hAB (v : V) (hv : v ∈ X) : v ∈ A ∨ v ∈ B := by
    simp only [A, B, Finset.mem_filter, hv, true_and]
    have hc := (C v).isLt
    omega
  have hA_sub : A ⊆ X := Finset.filter_subset _ _
  have hB_sub : B ⊆ X := Finset.filter_subset _ _
  have hA_arc_free {u v : V} (hu : u ∈ A) (hv : v ∈ A) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 0 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 0 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  have hB_arc_free {u v : V} (hu : u ∈ B) (hv : v ∈ B) : ¬ O.Arc u v := by
    intro huv
    have hcu : C u = 1 := (Finset.mem_filter.mp hu).2
    have hcv : C v = 1 := (Finset.mem_filter.mp hv).2
    exact C.valid (O.arc_adj huv) (hcu.trans hcv.symm)
  let candidates : Finset (Finset V) := A.powerset.filter (Admissible O B)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, Admissible]
  obtain ⟨S, hScand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hSA : S ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hScand).1
  have hSad : Admissible O B S := (Finset.mem_filter.mp hScand).2
  let T : Finset V := residual O B S
  let K : Finset V := S ∪ T
  have hTB : T ⊆ B := Finset.filter_subset _ _
  have hKX : K ⊆ X := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact hA_sub (hSA hvS)
    · exact hB_sub (hTB hvT)
  have hKind : ∀ u ∈ K, ∀ v ∈ K, ¬ O.Arc u v := by
    intro u hu v hv
    rcases Finset.mem_union.mp hu with huS | huT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact hA_arc_free (hSA huS) (hSA hvS)
      · exact hSad u huS v hvT
    · rcases Finset.mem_union.mp hv with hvS | hvT
      · exact (Finset.mem_filter.mp huT).2 v hvS
      · exact hB_arc_free (hTB huT) (hTB hvT)
  refine ⟨K, hKX, hKind, ?_⟩
  intro x hxX hxK
  rcases hAB x hxX with hxA | hxB
  · have hxS : x ∉ S := fun hx => hxK (Finset.mem_union_left T hx)
    have hex : ∃ b ∈ T, O.Arc x b := by
      by_contra! hnone
      have hres_sub : residual O B (insert x S) ⊆ T := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        apply Finset.mem_filter.mpr
        refine ⟨hb'.1, ?_⟩
        intro a haS
        exact hb'.2 a (Finset.mem_insert_of_mem haS)
      have hins_ad : Admissible O B (insert x S) := by
        intro a ha b hb
        rcases Finset.mem_insert.mp ha with rfl | haS
        · exact hnone b (hres_sub hb)
        · exact hSad a haS b (hres_sub hb)
      have hins_cand : insert x S ∈ candidates := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxA hSA), hins_ad⟩
      have hle := hmax (insert x S) hins_cand
      rw [Finset.card_insert_of_notMem hxS] at hle
      omega
    obtain ⟨b, hbT, hxb⟩ := hex
    exact ⟨b, Finset.mem_union_right S hbT, hxb⟩
  · have hxT : x ∉ T := fun hx => hxK (Finset.mem_union_right S hx)
    have hnot : ¬(∀ a ∈ S, ¬ O.Arc x a) := by
      intro h
      exact hxT (Finset.mem_filter.mpr ⟨hxB, h⟩)
    push Not at hnot
    obtain ⟨a, haS, hxa⟩ := hnot
    exact ⟨a, Finset.mem_union_left T haS, hxa⟩

end PlanarListColoring
