import MerLeanExperiment.FiniteFourier

namespace ReciprocalSquares

/-- A total weight exceeding the maximum possible single weight requires
at least two distinct elements. Individual weights need not be positive. -/
theorem two_elements_of_sum_gt_bound {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (w : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ x ∈ F, w x ≤ B)
    (hmass : B < ∑ x ∈ F, w x) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y := by
  apply Finset.one_lt_card.mp
  by_contra hcard
  have hc : F.card ≤ 1 := by omega
  have hsum : ∑ x ∈ F, w x ≤ (F.card : ℝ) * B := by
    calc
      ∑ x ∈ F, w x ≤ ∑ _x ∈ F, B := Finset.sum_le_sum hw
      _ = (F.card : ℝ) * B := by simp
  have hcr : (F.card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

theorem bernWeight_le_max_pow (D S : Finset ℕ) (p : ℝ)
    (hS : S ⊆ D) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernWeight D S p ≤ (max p (1 - p)) ^ D.card := by
  have hcard : S.card + (D \ S).card = D.card := by
    simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hS
  unfold bernWeight
  calc
    p ^ S.card * (1 - p) ^ (D \ S).card ≤
        (max p (1 - p)) ^ S.card * (max p (1 - p)) ^ (D \ S).card := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = (max p (1 - p)) ^ D.card := by rw [← pow_add, hcard]

end ReciprocalSquares
