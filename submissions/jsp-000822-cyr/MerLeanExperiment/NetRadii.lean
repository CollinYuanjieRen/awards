import MerLeanExperiment.NetGeometry

namespace DiskDiscrepancy

/-- Two enumerated mesh radii sandwich a disk even after a center error of two mesh units. -/
theorem exists_sandwich_mesh_radii {R r : ℝ} {q K : ℕ}
    (hR : 4 ≤ R) (hr : 4 ≤ r) (hrR : r ≤ R) (hq : R ≤ q)
    (hK : (q : ℝ) * (R + 1) ≤ K) :
    ∃ a b : Fin K,
      0 < (a.val : ℝ) / q ∧ (b.val : ℝ) / q ≤ R + 1 ∧
      (a.val : ℝ) / q + 2 / q ≤ r ∧ r + 2 / q ≤ (b.val : ℝ) / q ∧
      (b.val : ℝ) / q ≤ r + 3 / q ∧ r - 3 / q ≤ (a.val : ℝ) / q := by
  have hq4 : (4 : ℝ) ≤ q := hR.trans hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hr0 : 0 ≤ r := by linarith
  let n := ⌊(q : ℝ) * r⌋₊
  have hnlow : (n : ℝ) ≤ (q : ℝ) * r := Nat.floor_le (mul_nonneg hq0.le hr0)
  have hnhigh : (q : ℝ) * r < n + 1 := Nat.lt_floor_add_one _
  have hn3 : 3 ≤ n := Nat.le_floor (by norm_num; nlinarith)
  have hnK : n + 3 < K := by
    have hqr := mul_le_mul_of_nonneg_left hrR hq0.le
    have hreal : (n : ℝ) + 3 < K := by nlinarith
    exact_mod_cast hreal
  have hsub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  refine ⟨⟨n - 2, by omega⟩, ⟨n + 3, hnK⟩, ?_⟩
  simp only [Nat.cast_add, Nat.cast_ofNat, hsub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply div_pos _ hq0
    have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  · apply (div_le_iff₀ hq0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrR hq0.le]
  · rw [← add_div]
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  · apply (le_div_iff₀ hq0).mpr
    have heq : (r + 2 / (q : ℝ)) * q = r * q + 2 := by field_simp
    rw [heq]
    nlinarith
  · apply (div_le_iff₀ hq0).mpr
    have heq : (r + 3 / (q : ℝ)) * q = r * q + 3 := by field_simp
    rw [heq]
    nlinarith
  · apply (le_div_iff₀ hq0).mpr
    have heq : (r - 3 / (q : ℝ)) * q = r * q - 3 := by field_simp
    rw [heq]
    nlinarith

end DiskDiscrepancy
