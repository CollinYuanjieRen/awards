import MerLeanExperiment.RadiusTransfer

namespace DiskDiscrepancy

noncomputable def centerGridPoint (L q : ℕ) (v : Fin (L * q) × Fin (L * q)) : Plane :=
  WithLp.toLp 2 ![(v.1.val : ℝ) / q, (v.2.val : ℝ) / q]

theorem exists_mesh_coordinate {L q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx0 : 0 ≤ x) (hxL : x < L) :
    ∃ n : Fin (L * q), (n.val : ℝ) / q ≤ x ∧ x < (n.val : ℝ) / q + 1 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hxq : 0 ≤ (q : ℝ) * x := mul_nonneg hq0.le hx0
  have hn : ⌊(q : ℝ) * x⌋₊ < L * q := (Nat.floor_lt hxq).mpr (by
    simp only [Nat.cast_mul]
    nlinarith)
  refine ⟨⟨⌊(q : ℝ) * x⌋₊, hn⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hq0).mpr (by simpa [mul_comm] using Nat.floor_le hxq)
  · have h := Nat.lt_floor_add_one ((q : ℝ) * x)
    rw [← add_div]
    apply (lt_div_iff₀ hq0).mpr
    simpa [mul_comm] using h

/-- The finite square mesh approximates every center in a fundamental square. -/
theorem exists_centerGridPoint {L q : ℕ} (hq : 0 < q) {x : Plane}
    (hx : ∀ i : Fin 2, 0 ≤ x i ∧ x i < L) :
    ∃ v : Fin (L * q) × Fin (L * q), dist x (centerGridPoint L q v) ≤ 2 / q := by
  obtain ⟨v0,h0,h0'⟩ := exists_mesh_coordinate hq (hx 0).1 (hx 0).2
  obtain ⟨v1,h1,h1'⟩ := exists_mesh_coordinate hq (hx 1).1 (hx 1).2
  refine ⟨(v0,v1), ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hnorm := EuclideanSpace.real_norm_sq_eq (x - centerGridPoint L q (v0,v1))
  simp [centerGridPoint, Fin.sum_univ_two] at hnorm
  rw [dist_eq_norm]
  have hdiff0 : 0 ≤ x 0 - (v0.val : ℝ) / q := sub_nonneg.mpr h0
  have hdiff1 : 0 ≤ x 1 - (v1.val : ℝ) / q := sub_nonneg.mpr h1
  have hsq0 := pow_le_pow_left₀ hdiff0 (by linarith : x 0 - (v0.val : ℝ) / q ≤ 1 / q) 2
  have hsq1 := pow_le_pow_left₀ hdiff1 (by linarith : x 1 - (v1.val : ℝ) / q ≤ 1 / q) 2
  have hb : 0 ≤ (2 : ℝ) / q := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hb).mp
  dsimp [centerGridPoint] at *
  calc
    _ ≤ 2 * (1 / (q : ℝ)) ^ 2 := by nlinarith
    _ ≤ (2 / (q : ℝ)) ^ 2 := by
      rw [show (2 / (q : ℝ)) ^ 2 = 4 * (1 / (q : ℝ)) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)

/-- A fixed mesh-width shell contributes only a universal area error. -/
theorem mesh_shell_bound {R r q : ℝ} (hR : 4 ≤ R) (hr : r ≤ R) (hq : R ≤ q) :
    2 * r * (3 / q) + (3 / q) ^ 2 ≤ 8 := by
  have hq0 : 0 < q := by linarith
  have heq : 2 * r * (3 / q) + (3 / q) ^ 2 = (6 * r * q + 9) / q ^ 2 := by
    field_simp; ring
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
  have hmul := mul_le_mul_of_nonneg_right (hr.trans hq) hq0.le
  nlinarith [sq_nonneg (q - 4)]

end DiskDiscrepancy
