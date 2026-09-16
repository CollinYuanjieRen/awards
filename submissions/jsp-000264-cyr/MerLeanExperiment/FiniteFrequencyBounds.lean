import MerLeanExperiment.FrequencyCount
import Mathlib.Analysis.Complex.Basic

namespace ReciprocalSquares

/-- Count bounded frequencies by an interval, and the remaining ones by the modulus. -/
theorem sum_norm_outside_small_le (m L K : ℕ) [NeZero m]
    (f : ZMod m → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbounded : ∀ h : ZMod m, L < h.valMinAbs.natAbs →
      h.valMinAbs.natAbs ≤ K → ‖f h‖ ≤ a)
    (hhigh : ∀ h : ZMod m, K < h.valMinAbs.natAbs → ‖f h‖ ≤ b) :
    (∑ h ∈ Finset.univ.filter (fun h : ZMod m => L < h.valMinAbs.natAbs), ‖f h‖) ≤
      (2 * (K : ℝ) + 1) * a + (m : ℝ) * b := by
  classical
  let F := Finset.univ.filter (fun h : ZMod m => L < h.valMinAbs.natAbs)
  let B := F.filter (fun h => h.valMinAbs.natAbs ≤ K)
  let C := F.filter (fun h => ¬h.valMinAbs.natAbs ≤ K)
  have hBcard : B.card ≤ 2 * K + 1 := by
    apply le_trans _ (card_bounded_centered_frequencies m K)
    apply Finset.card_le_card
    intro h hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
  have hCcard : C.card ≤ m := by
    have := Finset.card_le_card (Finset.subset_univ C)
    simpa using this
  have hBsum : (∑ h ∈ B, ‖f h‖) ≤ (2 * (K : ℝ) + 1) * a := by
    calc
      (∑ h ∈ B, ‖f h‖) ≤ ∑ _h ∈ B, a := by
        apply Finset.sum_le_sum
        intro h hh
        obtain ⟨hhF, hhK⟩ := Finset.mem_filter.mp hh
        exact hbounded h (Finset.mem_filter.mp hhF).2 hhK
      _ = (B.card : ℝ) * a := by simp
      _ ≤ (2 * (K : ℝ) + 1) * a :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) ha
  have hCsum : (∑ h ∈ C, ‖f h‖) ≤ (m : ℝ) * b := by
    calc
      (∑ h ∈ C, ‖f h‖) ≤ ∑ _h ∈ C, b := by
        apply Finset.sum_le_sum
        intro h hh
        exact hhigh h (Nat.lt_of_not_ge (Finset.mem_filter.mp hh).2)
      _ = (C.card : ℝ) * b := by simp
      _ ≤ (m : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hCcard) hb
  have hsplit := Finset.sum_filter_add_sum_filter_not F
    (fun h : ZMod m => h.valMinAbs.natAbs ≤ K) (fun h => ‖f h‖)
  change (∑ h ∈ B, ‖f h‖) + (∑ h ∈ C, ‖f h‖) = _ at hsplit
  change (∑ h ∈ F, ‖f h‖) ≤ _
  linarith

end ReciprocalSquares
