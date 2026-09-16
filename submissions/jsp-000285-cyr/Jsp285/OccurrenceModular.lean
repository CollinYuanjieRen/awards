import Jsp285.OccurrenceSums
import ErdosProblems.Erdos344

/-! Modular completeness using distinct occurrence indices, with repeated weights allowed. -/

namespace Jsp285

open scoped BigOperators

/-- Divisor diversity of the occurrence weights forces their subset sums to
cover every residue modulo `q`.  Occurrences remain distinguished even when
several of them have the same weight. -/
theorem occurrenceSums_mod_eq_univ_of_divisor_diverse
    {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q]
    (hq : 0 < q) (v : ι → ℕ) (I : Finset ι)
    (hdiverse : ∀ e : ℕ, 1 < e → e ∣ q →
      e - 1 ≤ (I.filter fun i => ¬ e ∣ v i).card) :
    (occurrenceSums v I).image (fun x : ℕ => (x : ZMod q)) = Finset.univ := by
  have hlist :
      Erdos587.listSubsetSums
          (I.toList.map fun i => (v i : ZMod q)) = Finset.univ := by
    have h := Erdos344.listSubsetSums_mod_eq_univ_of_divisor_diverse
      hq (I.toList.map v) (by
        intro e he heq
        have hlen :
            ((I.toList.map v).filter fun a => ¬ e ∣ a).length =
              (I.filter fun i => ¬ e ∣ v i).card := by
          rw [List.filter_map, List.length_map]
          have hc := I.nodup_toList.card_eq_countP
            (P := fun i => ¬ e ∣ v i)
          simpa [List.countP_eq_length_filter, Function.comp_def] using hc.symm
        rw [hlen]
        exact hdiverse e he heq)
    simpa [List.map_map, Function.comp_def] using h
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  have hz : z ∈ Erdos587.listSubsetSums
      (I.toList.map fun i => (v i : ZMod q)) := by
    rw [hlist]
    exact Finset.mem_univ z
  obtain ⟨T, hTI, hTsum⟩ :=
    Erdos587.mem_listSubsetSums_iff.mp hz
  obtain ⟨U, hUI, rfl⟩ :=
    (List.sublist_map_iff (l₂ := I.toList)
      (f := fun i => (v i : ZMod q))).mp hTI
  refine Finset.mem_image.mpr ⟨U.toFinset.sum v, ?_, ?_⟩
  · apply mem_occurrenceSums.mpr
    refine ⟨U.toFinset, ?_, rfl⟩
    intro i hi
    exact Finset.mem_toList.mp (hUI.mem (List.mem_toFinset.mp hi))
  · rw [List.sum_toFinset v (I.nodup_toList.sublist hUI)]
    simpa [Function.comp_def] using hTsum

end Jsp285
