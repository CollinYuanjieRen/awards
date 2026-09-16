import MerLeanExperiment.BlockIndices
import MerLeanExperiment.ConstantTail
import MerLeanExperiment.GlobalDivisionSequence
import MerLeanExperiment.GlobalSignTail
import MerLeanExperiment.FiniteDivisionFamily

open Classical Filter MeasureTheory Set
open scoped Topology

namespace Erdos492Real

noncomputable section

/-- The actual sequence of glued divisions fails uniform distribution for
almost every positive dilation. The same family and sequence are fixed before
the dilation is chosen. -/
theorem ae_not_uniformlyDistributed_from_family (P : ℕ → FiniteDivision)
    (E : ℕ → Set ℝ) (hFine : ∀ k, (P k).Fine (blockEpsilon k))
    (hMeasure : ∀ k, volume (E k) < ENNReal.ofReal (blockEpsilon k))
    (hInvariant : ∀ k, ∀ x : ℝ, 0 ≤ x → x < 1 → x ∉ E k →
      ∀ m : ℕ, 1 ≤ m → m ≤ blockCutoff (k + 1) → (m : ℝ) * x < 1 →
        divisionSign ((P k).points : Set ℝ) ((m : ℝ) * x) =
          divisionSign ((P k).points : Set ℝ) x)
    {a : ℕ → ℝ} (hrange : range a = globalEndpoints P) (hmono : StrictMono a) :
    ∀ᵐ α : ℝ, 0 < α → ¬ UniformlyDistributed a α := by
  filter_upwards [ae_eventually_avoids_scaledExceptional E hMeasure] with α havoid
  intro hα
  obtain ⟨b, hb, hαlo, hαhi⟩ := exists_nat_scale_bounds hα
  have hbpos : 0 < b := by omega
  apply not_uniformlyDistributed_of_large_signedMean
  intro ε hε R
  have hindex : ∀ᶠ k in atTop, max R 1 ≤ blockUpperIndex k b :=
    tendsto_blockUpperIndex b hbpos (eventually_ge_atTop (max R 1))
  have hcutoff : ∀ᶠ k in atTop, b ≤ blockCutoff (k + 1) :=
    tendsto_blockCutoff_succ (eventually_ge_atTop b)
  have hkb : ∀ᶠ k : ℕ in atTop, b ≤ k + 2 :=
    eventually_atTop.mpr ⟨b, fun k hk => by omega⟩
  have herror : ∀ᶠ k in atTop,
      2 * (blockLowerIndex k : ℝ) / (blockUpperIndex k b : ℝ) < ε :=
    (tendsto_order.mp (tendsto_block_index_error b hbpos)).2 ε hε
  have hevent : ∀ᶠ _k : ℕ in atTop,
      ∃ N : ℕ, R ≤ N ∧ |signedMean a α N| > 1 - ε := by
    filter_upwards [havoid, hindex, hcutoff, hkb, herror,
      eventually_blockLowerIndex_le_upperIndex b hbpos]
      with k hkavoid hkindex hkcutoff hkb hkerror hkorder
    let c := divisionSign ((P k).points : Set ℝ)
      (α / (blockCutoff (k + 1) : ℝ))
    have hc : c = 1 ∨ c = -1 := by
      dsimp [c, divisionSign]
      split <;> simp
    have hNpos : 0 < blockUpperIndex k b := by omega
    have hbound := signedMean_abs_lower_bound_of_constant_tail a α c hc hkorder hNpos
      (fun m hm => by
        have hmlo : blockLowerIndex k ≤ m := by
          have := (Finset.mem_Icc.mp hm).1
          omega
        have hmhi := (Finset.mem_Icc.mp hm).2
        obtain ⟨hxlo, hxhi, hmB⟩ :=
          block_index_window hb hkb hαlo hαhi hkcutoff hmlo hmhi
        have hm1 : 1 ≤ m := by
          have := (Finset.mem_Icc.mp hm).1
          omega
        have hseq := sequence_sample_sign_eq P hrange hmono ((m : ℝ) * α)
        have hglobal := global_sample_sign_eq P hFine E k (hInvariant k)
          hα hkavoid hm1 hmB hxlo hxhi
        simpa only [one_div, c] using hseq.trans hglobal)
    exact ⟨blockUpperIndex k b, (le_max_left _ _).trans hkindex,
      lt_of_lt_of_le (sub_lt_sub_left hkerror 1) hbound⟩
  obtain ⟨k, hk⟩ := hevent.exists
  exact hk

/-- The global consequence of the finite subdivision lemma. This dependency
is explicit here and is discharged by the constructed finite lemma in the
unconditional public root. -/
theorem schmidt_counterexample_of_finite_subdivision
    (hfinite : FiniteSubdivisionLemma) : SchmidtStatement := by
  obtain ⟨P, E, hFine, _hMeasurable, hMeasure, hInvariant⟩ :=
    exists_finite_division_family hfinite
  obtain ⟨a, ha0, hmono, hatop, hratio, hrange, _hregions⟩ :=
    exists_global_division_sequence P hFine
  exact ⟨a, ha0, hmono, hatop, hratio,
    ae_not_uniformlyDistributed_from_family P E hFine hMeasure hInvariant hrange hmono⟩

end

end Erdos492Real
