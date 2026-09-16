import MerLeanExperiment.NetRadii

namespace DiskDiscrepancy

/-- A single finite center/radius grid controls all radii at least four in its fundamental square. -/
theorem discrepancy_on_square_of_net {S : Set Plane} (hS : Admissible S)
    {L q K : ℕ} {R D : ℝ} (hR : 4 ≤ R) (hq : R ≤ q)
    (hK : (q : ℝ) * (R + 1) ≤ K)
    (hnet : ∀ v : Fin (L * q) × Fin (L * q), ∀ j : Fin K,
      0 < (j.val : ℝ) / q → (j.val : ℝ) / q ≤ R + 1 →
      discrepancy S (centerGridPoint L q v) ((j.val : ℝ) / q) ≤ D)
    {x : Plane} (hx : ∀ i : Fin 2, 0 ≤ x i ∧ x i < L)
    {r : ℝ} (hr : 4 ≤ r) (hrR : r ≤ R) :
    discrepancy S x r ≤ D + 8 * Real.pi := by
  have hqpos : 0 < q := by
    have hqr : (0 : ℝ) < q := by linarith
    exact_mod_cast hqr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  obtain ⟨v,hv⟩ := exists_centerGridPoint hqpos hx
  obtain ⟨a,b,ha,hb,has,hat,hbt,hsa⟩ := exists_sandwich_mesh_radii hR hr hrR hq hK
  have hb0 : 0 < (b.val : ℝ) / q := by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hq0]
  have haR : (a.val : ℝ) / q ≤ R + 1 := by
    have : 0 ≤ (2 : ℝ) / q := by positivity
    linarith
  have h := discrepancy_le_of_nearby_radii hS (by linarith : 0 ≤ r) ha.le
    (by positivity : 0 ≤ 3 / (q : ℝ)) hv has hat hbt hsa
    (hnet v a ha haR) (hnet v b hb0 hb)
  have hshell := mesh_shell_bound hR hrR hq
  nlinarith [mul_le_mul_of_nonneg_left hshell Real.pi_pos.le]

end DiskDiscrepancy
