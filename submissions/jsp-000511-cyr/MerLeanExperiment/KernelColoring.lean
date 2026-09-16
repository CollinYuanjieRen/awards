/-
Copyright (c) 2026 The Lean-Proofs Authors. All rights reserved.
Released under Apache 2.0 license.
Adapted from plby/lean-proofs commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos630.lean. Formal authors: Codex, GPT-5.6 Sol.
Mathematical argument: Alon and Tarsi (1992).
-/
import MerLeanExperiment.Kernels

open Finset
open scoped SimpleGraph
namespace PlanarListColoring
universe u
variable {V : Type u}
noncomputable local instance decidableEqForKernelColoring : DecidableEq V := Classical.decEq V

/-! ## The kernel list-colouring lemma -/

/-- A kernel for every finite induced vertex set, together with the local
strict list-size bound, colours any finite active vertex set.  The result is
stated with a total colour function; its guarantees concern the active set. -/
theorem exists_list_coloring_on
    {G : SimpleGraph V} (O : TwoOrientation G)
    (hkernel : ∀ X : Finset V, ∃ K : Finset V, IsKernel O X K)
    (L : V → Finset ℕ) (U : Finset V)
    (hcap : ∀ v ∈ U, (O.outNeighbors U v).card < (L v).card) :
    ∃ f : V → ℕ,
      (∀ v ∈ U, f v ∈ L v) ∧
      ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → f u ≠ f v := by
  classical
  induction U using Finset.strongInduction generalizing L with
  | H U ih =>
      by_cases hUne : U.Nonempty
      · obtain ⟨u₀, hu₀U⟩ := hUne
        have hLpos : 0 < (L u₀).card :=
          (Nat.zero_le (O.outNeighbors U u₀).card).trans_lt (hcap u₀ hu₀U)
        have hLne : (L u₀).Nonempty := Finset.card_pos.mp hLpos
        let c : ℕ := (L u₀).min' hLne
        have hcL : c ∈ L u₀ := Finset.min'_mem (L u₀) hLne
        let X : Finset V := U.filter fun v => c ∈ L v
        have hu₀X : u₀ ∈ X := Finset.mem_filter.mpr ⟨hu₀U, hcL⟩
        obtain ⟨K, hK⟩ := hkernel X
        have hKne : K.Nonempty := by
          by_contra h
          have hKempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          obtain ⟨k, hkK, -⟩ := hK.absorbs hu₀X (by simp [hKempty])
          simp [hKempty] at hkK
        let U' : Finset V := U \ K
        let L' : V → Finset ℕ := fun v => (L v).erase c
        have hKsubU : K ⊆ U := by
          exact hK.subset.trans (Finset.filter_subset _ _)
        have hU'ssub : U' ⊂ U := Finset.sdiff_ssubset hKsubU hKne
        have hcap' : ∀ v ∈ U', (O.outNeighbors U' v).card < (L' v).card := by
          intro v hvU'
          have hvU : v ∈ U := Finset.sdiff_subset hvU'
          have houtsub : O.outNeighbors U' v ⊆ O.outNeighbors U v :=
            O.outNeighbors_mono Finset.sdiff_subset v
          by_cases hcv : c ∈ L v
          · have hvX : v ∈ X := Finset.mem_filter.mpr ⟨hvU, hcv⟩
            have hvK : v ∉ K := (Finset.mem_sdiff.mp hvU').2
            obtain ⟨k, hkK, hvk⟩ := hK.absorbs hvX hvK
            have hkU : k ∈ U := hKsubU hkK
            have hkout : k ∈ O.outNeighbors U v :=
              O.mem_outNeighbors.mpr ⟨hkU, hvk⟩
            have hkout' : k ∉ O.outNeighbors U' v := by
              intro hk
              exact (Finset.mem_sdiff.mp (O.mem_outNeighbors.mp hk).1).2 hkK
            have houtssub : O.outNeighbors U' v ⊂ O.outNeighbors U v :=
              Finset.ssubset_iff_subset_ne.mpr ⟨houtsub, fun heq => hkout' (heq ▸ hkout)⟩
            have houtlt := Finset.card_lt_card houtssub
            have hLcard : (L' v).card = (L v).card - 1 := by
              exact Finset.card_erase_of_mem hcv
            have holdlt := hcap v hvU
            dsimp only [L'] at hLcard ⊢
            omega
          · have hL'eq : L' v = L v := by simp [L', hcv]
            rw [hL'eq]
            exact (Finset.card_mono houtsub).trans_lt (hcap v hvU)
        obtain ⟨f, hfL, hfproper⟩ := ih U' hU'ssub L' hcap'
        let g : V → ℕ := fun v => if v ∈ K then c else f v
        refine ⟨g, ?_, ?_⟩
        · intro v hvU
          by_cases hvK : v ∈ K
          · simp only [g, ite_eq_left hvK]
            have hvX : v ∈ X := hK.subset hvK
            exact (Finset.mem_filter.mp hvX).2
          · simp only [g, ite_eq_right hvK]
            have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
            exact Finset.mem_of_mem_erase (hfL v hvU')
        · intro u huU v hvU huv
          by_cases huK : u ∈ K
          · by_cases hvK : v ∈ K
            · exact (hK.isIndepSet huK hvK huv.ne huv).elim
            · simp only [g, ite_eq_left huK, ite_eq_right hvK]
              have hvU' : v ∈ U' := Finset.mem_sdiff.mpr ⟨hvU, hvK⟩
              exact (Finset.mem_erase.mp (hfL v hvU')).1.symm
          · by_cases hvK : v ∈ K
            · simp only [g, ite_eq_right huK, ite_eq_left hvK]
              have huU' : u ∈ U' := Finset.mem_sdiff.mpr ⟨huU, huK⟩
              exact (Finset.mem_erase.mp (hfL u huU')).1
            · simp only [g, ite_eq_right huK, ite_eq_right hvK]
              exact hfproper u (Finset.mem_sdiff.mpr ⟨huU, huK⟩)
                v (Finset.mem_sdiff.mpr ⟨hvU, hvK⟩) huv
      · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro v hv
          exfalso
          simp [hUempty] at hv
        · intro u hu
          exfalso
          simp [hUempty] at hu

end PlanarListColoring
