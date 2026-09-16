import Jsp285.ExtractionBounds
import Jsp285.OccurrencePrune
import Jsp285.FiniteConstants

/-! Extraction and pruning retain linearly many diverse occurrence indices. -/

namespace Jsp285

/-- Filtering a subset loses no more elements than were removed from the whole set. -/
lemma filter_card_loss_le {ι : Type*} [DecidableEq ι] {S Z : Finset ι}
    (hSZ : S ⊆ Z) (p : ι → Prop) [DecidablePred p] :
    (Z.filter p).card - (S.filter p).card ≤ Z.card - S.card := by
  rw [← Finset.card_sdiff_of_subset (Finset.filter_subset_filter p hSZ),
    ← Finset.card_sdiff_of_subset hSZ]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_filter] at hi ⊢
  tauto

/-- Absolute mass and diversity reserves after normalization and whole-bin pruning. -/
theorem exists_prepared_occurrences {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (v : ι → ℕ) (I : Finset ι)
    (hbox : ∀ i ∈ I, 0 < v i ∧ v i ≤ n)
    (hcount : finiteCoefficient * n ≤ I.card) :
    ∃ d : ℕ, ∃ S : Finset ι, ∃ w : ι → ℕ,
      0 < d ∧ d ≤ n ∧ S ⊆ I ∧
      (∀ i ∈ S, d * w i = v i) ∧
      (∀ i ∈ S, 0 < w i ∧ w i ≤ n / d) ∧
      39999 * partitionMass * n ≤ S.card ∧
      (∀ e : ℕ, 1 < e → d * e ≤ n →
        10000 * partitionMass * (Nat.log 2 n + 1) + partitionMass * e ≤
          (S.filter fun i ↦ ¬e ∣ w i).card) ∧
      (∀ j : ℕ, (dyadicBin w S j).Nonempty →
        10000 * partitionMass * (Nat.log 2 n + 1) ≤ (dyadicBin w S j).card) := by
  classical
  let H := partitionMass
  let r := Nat.log 2 n + 1
  let Q := 10000 * H * r
  let L := (r + 1) * Q
  obtain ⟨d, Z, w, hd, hdn, hZI, hscale, hloss, hdiv⟩ :=
    exists_divisorExtraction n L H hn I v
  have hnorm := normalized_weight_bounds hd hZI hbox hscale
  have hZbox : ∀ i ∈ Z, 0 < w i ∧ w i ≤ n := by
    intro i hi
    exact ⟨(hnorm i hi).1, (hnorm i hi).2.trans (Nat.div_le_self _ _)⟩
  let S := dyadicPrune w Z Q
  have hSZ : S ⊆ Z := dyadicPrune_subset w Z Q
  have hSI : S ⊆ I := hSZ.trans hZI
  have hprune : Z.card - S.card ≤ r * Q := card_sub_dyadicPrune_le w Z n Q hZbox
  have htotal : I.card - S.card ≤ 160001 * H * n := by
    have hZle := Finset.card_le_card hZI
    have hSle := Finset.card_le_card hSZ
    have hsplit : I.card - S.card = (I.card - Z.card) + (Z.card - S.card) := by
      omega
    rw [hsplit]
    exact (Nat.add_le_add hloss hprune).trans (extraction_prune_loss_bound n H hn)
  have hremaining : 39999 * H * n ≤ S.card := by
    change 200000 * H * n ≤ I.card at hcount
    have hnat : I.card ≤ (I.card - S.card) + S.card := by omega
    nlinarith
  refine ⟨d, S, w, hd, hdn, hSI, fun i hi ↦ hscale i (hSZ hi),
    fun i hi ↦ hnorm i (hSZ hi), hremaining, ?_, ?_⟩
  · intro e he hde
    have hstart := hdiv e he hde
    have hdiff := (filter_card_loss_le hSZ (fun i ↦ ¬e ∣ w i)).trans hprune
    have hformula : L = r * Q + Q := by dsimp [L]; ring
    change Q + H * e ≤ _
    rw [hformula] at hstart
    omega
  · intro j hj
    change Q ≤ (dyadicBin w S j).card
    dsimp only [S] at hj ⊢
    by_cases h : Q ≤ (dyadicBin w Z j).card
    · simp [dyadicBin_dyadicPrune, h]
    · rw [dyadicBin_dyadicPrune, if_neg h] at hj
      exact (Finset.not_nonempty_empty hj).elim

end Jsp285
