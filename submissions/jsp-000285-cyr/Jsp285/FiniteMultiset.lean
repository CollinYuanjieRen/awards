import Jsp285.BalancedOccurrences
import Jsp285.OccurrenceAP

/-! The finite multiset theorem, with every occurrence bridge discharged. -/

namespace Jsp285

/-- Linearly many occurrences in `[1,n]` have an `n`-term AP among their subset sums. -/
theorem finite_multiset_AP {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (v : ι → ℕ) (I : Finset ι)
    (hbox : ∀ i ∈ I, 0 < v i ∧ v i ≤ n)
    (hcount : finiteCoefficient * n ≤ I.card) :
    Erdos344.ContainsFiniteAP (occurrenceSums v I : Set ℕ) n := by
  obtain ⟨d, S, w, hd, hdn, hSI, hscale, hnorm, hSlarge, hdiv, hbin⟩ :=
    exists_prepared_occurrences n hn v I hbox hcount
  obtain ⟨T, hcarrier, hdisj, hleaf⟩ :=
    exists_balanced_occurrence_partition n d hn hd hdn w S hnorm hSlarge hdiv hbin
  have hmass : 39999 * partitionMass * n ≤ ∑ i ∈ S, w i := by
    apply hSlarge.trans
    calc
      S.card = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, w i := Finset.sum_le_sum fun i hi ↦ (hnorm i hi).1
  obtain ⟨a, e, he, hterms⟩ := containsAP_of_balanced_occurrence_tree
    w S (n / d) n hn hnorm hmass T hcarrier hdisj hleaf
  refine ⟨d * a, d * e, Nat.mul_pos hd he, ?_⟩
  intro j hj
  have hscaled := scale_mem_occurrenceSums hSI hscale (hterms j hj)
  change d * a + j * (d * e) ∈ occurrenceSums v I
  convert hscaled using 1
  ring

end Jsp285
