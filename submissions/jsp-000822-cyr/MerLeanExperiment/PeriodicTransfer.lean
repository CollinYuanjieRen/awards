import MerLeanExperiment.PeriodicGrid
import MerLeanExperiment.NetTransfer
import MerLeanExperiment.SmallRadii

namespace DiskDiscrepancy

theorem discrepancy_image_add (S : Set Plane) (v x : Plane) (r : ℝ) :
    discrepancy ((fun p ↦ p + v) '' S) (x + v) r = discrepancy S x r := by
  have heq : diskPoints ((fun p ↦ p + v) '' S) (x + v) r =
      (fun p ↦ p + v) '' diskPoints S x r := by
    ext p
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hd⟩
      exact ⟨z, ⟨hz, by simpa only [dist_add_right] using hd⟩, rfl⟩
    · rintro ⟨z,⟨hz,hd⟩,rfl⟩
      exact ⟨⟨z,hz,rfl⟩, by simpa only [dist_add_right] using hd⟩
  unfold discrepancy pointCount
  rw [heq, Set.ncard_image_of_injective _ (add_left_injective v)]

theorem exists_center_in_fundamental_square {L : ℕ} (hL : 0 < L) (x : Plane) :
    ∃ k : ℤ × ℤ, ∀ i : Fin 2,
      0 ≤ (x - periodVector L k) i ∧ (x - periodVector L k) i < L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨(⌊x 0 / L⌋, ⌊x 1 / L⌋), ?_⟩
  intro i
  fin_cases i
  · change 0 ≤ x 0 - (L : ℝ) * (⌊x 0 / L⌋ : ℤ) ∧
      x 0 - (L : ℝ) * (⌊x 0 / L⌋ : ℤ) < L
    have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x 0 / L)) hL0.le
    have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x 0 / L)) hL0
    have heq : x 0 / (L : ℝ) * L = x 0 := div_mul_cancel₀ _ hL0.ne'
    constructor <;> nlinarith
  · change 0 ≤ x 1 - (L : ℝ) * (⌊x 1 / L⌋ : ℤ) ∧
      x 1 - (L : ℝ) * (⌊x 1 / L⌋ : ℤ) < L
    have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x 1 / L)) hL0.le
    have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x 1 / L)) hL0
    have heq : x 1 / (L : ℝ) * L = x 1 := div_mul_cancel₀ _ hL0.ne'
    constructor <;> nlinarith

/-- Actual periodicity extends a common finite-net bound to all centers and all positive radii. -/
theorem periodic_grid_bound_of_net {L q K : ℕ} (hL : 0 < L) (hq : 0 < q)
    (ω : (Fin L × Fin L) → (Fin q × Fin q)) {R D : ℝ} (hR : 4 ≤ R)
    (hqR : R ≤ q) (hK : (q : ℝ) * (R + 1) ≤ K)
    (hnet : ∀ v : Fin (L * q) × Fin (L * q), ∀ j : Fin K,
      0 < (j.val : ℝ) / q → (j.val : ℝ) / q ≤ R + 1 →
      discrepancy (periodicGridSet L q hL hq ω) (centerGridPoint L q v) ((j.val : ℝ) / q) ≤ D) :
    ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
      discrepancy (periodicGridSet L q hL hq ω) x r ≤ D + 40 * Real.pi := by
  have hadm := admissible_periodicGridSet L q hL hq ω
  have hlarge (x : Plane) (r : ℝ) (hr : 4 ≤ r) (hrR : r ≤ R) :
      discrepancy (periodicGridSet L q hL hq ω) x r ≤ D + 8 * Real.pi := by
    obtain ⟨k,hk⟩ := exists_center_in_fundamental_square hL x
    have h := discrepancy_on_square_of_net hadm hR hqR hK hnet hk hr hrR
    have heq := discrepancy_image_add (periodicGridSet L q hL hq ω)
      (periodVector L k) (x - periodVector L k) r
    rw [periodicGridSet_add_period L q hL hq ω k, sub_add_cancel] at heq
    rwa [← heq] at h
  have h := all_positive_radii_of_four_le hadm hR hlarge
  intro x r hr hrR
  convert h x r hr hrR using 1
  ring

end DiskDiscrepancy
