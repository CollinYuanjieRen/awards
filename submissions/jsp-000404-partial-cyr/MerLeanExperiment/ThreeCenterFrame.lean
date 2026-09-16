import MerLeanExperiment.DirectionFrame
import Mathlib.Tactic

/-!
Explicit direction data for the three-center limiting construction.
-/

namespace PlanarMinimax

noncomputable def threeDelta (m : ℕ) : ℝ :=
  2 * Real.pi / (2 * (m : ℝ) + 1)

noncomputable def threeBeta (m : ℕ) : ℝ := threeDelta m / 2

noncomputable def centerA : Plane := !₂[0, 0]

noncomputable def centerB (m : ℕ) : Plane :=
  !₂[2 * Real.cos (threeBeta m), 0]

noncomputable def centerC (m : ℕ) : Plane :=
  !₂[Real.cos (threeBeta m), Real.sin (threeBeta m)]

noncomputable def threeCenter (m : ℕ) : Fin 3 → Plane
  | 0 => centerA
  | 1 => centerB m
  | 2 => centerC m

noncomputable def angleA (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  ((j : ℝ) + 3 / 2) * threeDelta m

noncomputable def angleB (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  ((j : ℝ) + 1) * threeDelta m

noncomputable def angleC (m : ℕ) (j : Fin (m - 2)) : ℝ :=
  ((j : ℝ) + 3 / 2) * threeDelta m

theorem threeDelta_pos {m : ℕ} : 0 < threeDelta m := by
  unfold threeDelta
  positivity

theorem threeBeta_pos {m : ℕ} : 0 < threeBeta m := by
  unfold threeBeta
  exact half_pos threeDelta_pos

theorem threeBeta_lt_pi_div_two {m : ℕ} (hm : 2 ≤ m) :
    threeBeta m < Real.pi / 2 := by
  unfold threeBeta threeDelta
  have hpi := Real.pi_pos
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  field_simp
  nlinarith

theorem threeDelta_le_pi {m : ℕ} (hm : 2 ≤ m) :
    threeDelta m ≤ Real.pi := by
  unfold threeDelta
  have hpi := Real.pi_pos
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  field_simp
  nlinarith

theorem cos_threeBeta_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < Real.cos (threeBeta m) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < Real.pi / 2 := by positivity
    linarith [threeBeta_pos (m := m)]
  · exact threeBeta_lt_pi_div_two hm

theorem sin_threeBeta_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < Real.sin (threeBeta m) := by
  apply Real.sin_pos_of_pos_of_lt_pi threeBeta_pos
  linarith [threeBeta_lt_pi_div_two hm, Real.pi_pos]

theorem centerB_sub_centerA (m : ℕ) :
    centerB m - centerA = (2 * Real.cos (threeBeta m)) • unitDirection 0 := by
  ext i
  fin_cases i <;> simp [centerA, centerB, unitDirection]

theorem centerC_sub_centerA (m : ℕ) :
    centerC m - centerA = unitDirection (threeBeta m) := by
  ext i
  fin_cases i <;> simp [centerA, centerC, unitDirection]

theorem centerA_sub_centerB (m : ℕ) :
    centerA - centerB m = (2 * Real.cos (threeBeta m)) • (-unitDirection 0) := by
  ext i
  fin_cases i <;> simp [centerA, centerB, unitDirection]

theorem centerC_sub_centerB (m : ℕ) :
    centerC m - centerB m = unitDirection (Real.pi - threeBeta m) := by
  ext i
  fin_cases i
  · simp [centerB, centerC, unitDirection, Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  · simp [centerB, centerC, unitDirection, Real.cos_pi_sub, Real.sin_pi_sub]

theorem centerA_sub_centerC (m : ℕ) :
    centerA - centerC m = -unitDirection (threeBeta m) := by
  ext i
  fin_cases i <;> simp [centerA, centerC, unitDirection]

theorem centerB_sub_centerC (m : ℕ) :
    centerB m - centerC m = unitDirection (-threeBeta m) := by
  ext i
  fin_cases i
  · simp [centerB, centerC, unitDirection, Real.cos_neg, Real.sin_neg]
    ring
  · simp [centerB, centerC, unitDirection, Real.cos_neg, Real.sin_neg]

theorem unitDirection_neg_beta (m : ℕ) :
    unitDirection (-threeBeta m) = -unitDirection (Real.pi - threeBeta m) := by
  ext i
  fin_cases i <;>
    simp [unitDirection, Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub]

theorem centerA_ne_centerB {m : ℕ} (hm : 2 ≤ m) : centerA ≠ centerB m := by
  intro h
  have h0 := congrArg (fun p : Plane ↦ p (0 : Fin 2)) h
  simp [centerA, centerB] at h0
  nlinarith [cos_threeBeta_pos hm]

theorem centerA_ne_centerC {m : ℕ} (hm : 2 ≤ m) : centerA ≠ centerC m := by
  intro h
  have h1 := congrArg (fun p : Plane ↦ p (1 : Fin 2)) h
  simp [centerA, centerC] at h1
  nlinarith [sin_threeBeta_pos hm]

theorem centerB_ne_centerC {m : ℕ} (hm : 2 ≤ m) : centerB m ≠ centerC m := by
  intro h
  have h1 := congrArg (fun p : Plane ↦ p (1 : Fin 2)) h
  simp [centerB, centerC] at h1
  nlinarith [sin_threeBeta_pos hm]

theorem threeCenter_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (threeCenter m) := by
  have hAB := centerA_ne_centerB hm
  have hAC := centerA_ne_centerC hm
  have hBC := centerB_ne_centerC hm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [threeCenter]

theorem angle_centers_at_A {m : ℕ} (hm : 2 ≤ m) :
    EuclideanGeometry.angle (centerB m) centerA (centerC m) = threeBeta m := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub, centerB_sub_centerA, centerC_sub_centerA]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _
    (mul_pos (by norm_num) (cos_threeBeta_pos hm))]
  have hβpi : threeBeta m ≤ Real.pi := by
    linarith [threeBeta_pos (m := m), threeBeta_lt_pi_div_two hm, Real.pi_pos]
  simpa [abs_of_nonneg (threeBeta_pos (m := m)).le] using
    angle_unitDirection 0 (threeBeta m)
      (by simpa [abs_of_nonneg (threeBeta_pos (m := m)).le] using hβpi)

theorem angle_centers_at_B {m : ℕ} (hm : 2 ≤ m) :
    EuclideanGeometry.angle centerA (centerB m) (centerC m) = threeBeta m := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub, centerA_sub_centerB, centerC_sub_centerB]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _
    (mul_pos (by norm_num) (cos_threeBeta_pos hm))]
  rw [InnerProductGeometry.angle_neg_left]
  have hβpi : threeBeta m ≤ Real.pi := by
    linarith [threeBeta_pos (m := m), threeBeta_lt_pi_div_two hm, Real.pi_pos]
  rw [angle_unitDirection 0 (Real.pi - threeBeta m)]
  · rw [abs_of_nonpos]
    · linarith
    · linarith
  · rw [abs_of_nonpos]
    · linarith [threeBeta_pos (m := m)]
    · linarith [threeBeta_pos (m := m), hβpi]

theorem angle_centers_at_C {m : ℕ} (hm : 2 ≤ m) :
    EuclideanGeometry.angle centerA (centerC m) (centerB m) =
      Real.pi - threeDelta m := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub, centerA_sub_centerC, centerB_sub_centerC]
  rw [InnerProductGeometry.angle_neg_left]
  have h2βpi : 2 * threeBeta m ≤ Real.pi := by
    calc
      2 * threeBeta m = threeDelta m := by unfold threeBeta; ring
      _ ≤ Real.pi := threeDelta_le_pi hm
  rw [angle_unitDirection (threeBeta m) (-threeBeta m)]
  · rw [abs_of_nonneg]
    · unfold threeBeta
      ring
    · linarith [threeBeta_pos (m := m)]
  · rw [abs_of_nonneg] <;> linarith [threeBeta_pos (m := m)]

theorem center_triangle_angles_le {m : ℕ} (hm : 2 ≤ m) :
    EuclideanGeometry.angle (centerB m) centerA (centerC m) ≤
        Real.pi - threeDelta m ∧
      EuclideanGeometry.angle centerA (centerB m) (centerC m) ≤
        Real.pi - threeDelta m ∧
      EuclideanGeometry.angle centerA (centerC m) (centerB m) ≤
        Real.pi - threeDelta m := by
  rw [angle_centers_at_A hm, angle_centers_at_B hm, angle_centers_at_C hm]
  have hβ : threeBeta m ≤ Real.pi - threeDelta m := by
    unfold threeBeta threeDelta
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    field_simp
    nlinarith [Real.pi_pos]
  exact ⟨hβ, hβ, le_rfl⟩

private theorem shiftedFrame_separation {m d : ℕ} (hm : 2 ≤ m)
    (hd : d ≤ m - 1) (c : ℝ) {i j : Fin d} (hij : i ≠ j) :
    threeDelta m ≤
        |((i : ℝ) + c) * threeDelta m - ((j : ℝ) + c) * threeDelta m| ∧
      |((i : ℝ) + c) * threeDelta m - ((j : ℝ) + c) * threeDelta m| ≤
        Real.pi - threeDelta m := by
  have hδ := threeDelta_pos (m := m)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd' : d ≤ m := le_trans hd (Nat.sub_le m 1)
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij'
    have hj : (j : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast j.isLt
    have hdmNat : d + 1 ≤ m := by omega
    have hdm : (d : ℝ) + 1 ≤ m := by exact_mod_cast hdmNat
    rw [abs_of_nonpos (by nlinarith)]
    constructor
    · nlinarith
    · unfold threeDelta
      field_simp
      nlinarith [Real.pi_pos]
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hji'
    have hi : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
    have hdmNat : d + 1 ≤ m := by omega
    have hdm : (d : ℝ) + 1 ≤ m := by exact_mod_cast hdmNat
    rw [abs_of_nonneg (by nlinarith)]
    constructor
    · nlinarith
    · unfold threeDelta
      field_simp
      nlinarith [Real.pi_pos]

theorem angleA_separation {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 1)}
    (hij : i ≠ j) :
    threeDelta m ≤ |angleA m i - angleA m j| ∧
      |angleA m i - angleA m j| ≤ Real.pi - threeDelta m := by
  exact shiftedFrame_separation hm le_rfl (3 / 2) hij

theorem angleB_separation {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 1)}
    (hij : i ≠ j) :
    threeDelta m ≤ |angleB m i - angleB m j| ∧
      |angleB m i - angleB m j| ≤ Real.pi - threeDelta m := by
  exact shiftedFrame_separation hm le_rfl 1 hij

theorem angleC_separation {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 2)}
    (hij : i ≠ j) :
    threeDelta m ≤ |angleC m i - angleC m j| ∧
      |angleC m i - angleC m j| ≤ Real.pi - threeDelta m := by
  apply shiftedFrame_separation hm _ (3 / 2) hij
  omega

theorem signed_angleA_le {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 1)}
    (hij : i ≠ j) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleA m i))
        (signedDirection τ (angleA m j)) ≤ Real.pi - threeDelta m := by
  exact angle_signedDirection_le σ τ _ _ _ (threeDelta_pos.le)
    (angleA_separation hm hij).1 (angleA_separation hm hij).2

theorem signed_angleB_le {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 1)}
    (hij : i ≠ j) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleB m i))
        (signedDirection τ (angleB m j)) ≤ Real.pi - threeDelta m := by
  exact angle_signedDirection_le σ τ _ _ _ (threeDelta_pos.le)
    (angleB_separation hm hij).1 (angleB_separation hm hij).2

theorem signed_angleC_le {m : ℕ} (hm : 2 ≤ m) {i j : Fin (m - 2)}
    (hij : i ≠ j) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleC m i))
        (signedDirection τ (angleC m j)) ≤ Real.pi - threeDelta m := by
  exact angle_signedDirection_le σ τ _ _ _ (threeDelta_pos.le)
    (angleC_separation hm hij).1 (angleC_separation hm hij).2

private theorem angleA_external_separation {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) :
    (threeDelta m ≤ |angleA m j - 0| ∧
      |angleA m j - 0| ≤ Real.pi - threeDelta m) ∧
    (threeDelta m ≤ |angleA m j - threeBeta m| ∧
      |angleA m j - threeBeta m| ≤ Real.pi - threeDelta m) := by
  have hjNat : j.val + 2 ≤ m := by omega
  have hj : (j : ℝ) + 2 ≤ m := by exact_mod_cast hjNat
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ := threeDelta_pos (m := m)
  have hA0 : 0 ≤ angleA m j - 0 := by unfold angleA; nlinarith
  have hAβ : 0 ≤ angleA m j - threeBeta m := by
    unfold angleA threeBeta
    nlinarith
  rw [abs_of_nonneg hA0, abs_of_nonneg hAβ]
  unfold angleA threeBeta threeDelta
  field_simp
  constructor <;> constructor <;> nlinarith [Real.pi_pos]

private theorem angleB_external_separation {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) :
    (threeDelta m ≤ |angleB m j - 0| ∧
      |angleB m j - 0| ≤ Real.pi - threeDelta m) ∧
    (threeDelta m ≤ |angleB m j - (Real.pi - threeBeta m)| ∧
      |angleB m j - (Real.pi - threeBeta m)| ≤ Real.pi - threeDelta m) := by
  have hjNat : j.val + 2 ≤ m := by omega
  have hj : (j : ℝ) + 2 ≤ m := by exact_mod_cast hjNat
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ := threeDelta_pos (m := m)
  have hB0 : 0 ≤ angleB m j - 0 := by unfold angleB; nlinarith
  have hBπ : angleB m j - (Real.pi - threeBeta m) ≤ 0 := by
    unfold angleB threeBeta threeDelta
    field_simp
    nlinarith [Real.pi_pos]
  rw [abs_of_nonneg hB0, abs_of_nonpos hBπ]
  unfold angleB threeBeta threeDelta
  field_simp
  constructor <;> constructor <;> nlinarith [Real.pi_pos]

private theorem angleC_external_separation {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 2)) :
    (threeDelta m ≤ |angleC m j - threeBeta m| ∧
      |angleC m j - threeBeta m| ≤ Real.pi - threeDelta m) ∧
    (threeDelta m ≤ |angleC m j - (Real.pi - threeBeta m)| ∧
      |angleC m j - (Real.pi - threeBeta m)| ≤ Real.pi - threeDelta m) := by
  have hj : (j : ℝ) + 1 ≤ m - 2 := by
    have := j.isLt
    exact_mod_cast this
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ := threeDelta_pos (m := m)
  have hCβ : 0 ≤ angleC m j - threeBeta m := by
    unfold angleC threeBeta
    nlinarith
  have hCπ : angleC m j - (Real.pi - threeBeta m) ≤ 0 := by
    unfold angleC threeBeta threeDelta
    field_simp
    nlinarith [Real.pi_pos]
  rw [abs_of_nonneg hCβ, abs_of_nonpos hCπ]
  unfold angleC threeBeta threeDelta
  field_simp
  constructor <;> constructor <;> nlinarith [Real.pi_pos]

theorem signed_angleA_external_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleA m j))
        (signedDirection τ 0) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleA m j))
        (signedDirection τ (threeBeta m)) ≤ Real.pi - threeDelta m := by
  constructor
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleA_external_separation hm j).1.1 (angleA_external_separation hm j).1.2
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleA_external_separation hm j).2.1 (angleA_external_separation hm j).2.2

theorem signed_angleB_external_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleB m j))
        (signedDirection τ 0) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleB m j))
        (signedDirection τ (Real.pi - threeBeta m)) ≤ Real.pi - threeDelta m := by
  constructor
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleB_external_separation hm j).1.1 (angleB_external_separation hm j).1.2
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleB_external_separation hm j).2.1 (angleB_external_separation hm j).2.2

theorem signed_angleC_external_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 2)) (σ τ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleC m j))
        (signedDirection τ (threeBeta m)) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleC m j))
        (signedDirection τ (Real.pi - threeBeta m)) ≤ Real.pi - threeDelta m := by
  constructor
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleC_external_separation hm j).1.1 (angleC_external_separation hm j).1.2
  · exact angle_signedDirection_le σ τ _ _ _ threeDelta_pos.le
      (angleC_external_separation hm j).2.1 (angleC_external_separation hm j).2.2

theorem angleA_center_displacements_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) (σ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleA m j))
        (centerB m - centerA) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleA m j))
        (centerC m - centerA) ≤ Real.pi - threeDelta m := by
  rw [centerB_sub_centerA, centerC_sub_centerA,
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (mul_pos (by norm_num) (cos_threeBeta_pos hm))]
  simpa [signedDirection] using signed_angleA_external_le hm j σ true

theorem angleB_center_displacements_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 1)) (σ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleB m j))
        (centerA - centerB m) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleB m j))
        (centerC m - centerB m) ≤ Real.pi - threeDelta m := by
  rw [centerA_sub_centerB, centerC_sub_centerB,
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (mul_pos (by norm_num) (cos_threeBeta_pos hm))]
  constructor
  · simpa [signedDirection] using (signed_angleB_external_le hm j σ false).1
  · simpa [signedDirection] using (signed_angleB_external_le hm j σ true).2

theorem angleC_center_displacements_le {m : ℕ} (hm : 2 ≤ m)
    (j : Fin (m - 2)) (σ : Bool) :
    InnerProductGeometry.angle (signedDirection σ (angleC m j))
        (centerA - centerC m) ≤ Real.pi - threeDelta m ∧
      InnerProductGeometry.angle (signedDirection σ (angleC m j))
        (centerB m - centerC m) ≤ Real.pi - threeDelta m := by
  rw [centerA_sub_centerC, centerB_sub_centerC, unitDirection_neg_beta]
  simpa [signedDirection] using signed_angleC_external_le hm j σ false

#print axioms threeDelta_pos
#print axioms threeBeta_lt_pi_div_two
#print axioms angleA_separation
#print axioms angleB_separation
#print axioms angleC_separation
#print axioms signed_angleA_le
#print axioms signed_angleB_le
#print axioms signed_angleC_le
#print axioms signed_angleA_external_le
#print axioms signed_angleB_external_le
#print axioms signed_angleC_external_le
#print axioms angleA_center_displacements_le
#print axioms angleB_center_displacements_le
#print axioms angleC_center_displacements_le
#print axioms threeCenter_injective
#print axioms angle_centers_at_A
#print axioms angle_centers_at_B
#print axioms angle_centers_at_C
#print axioms center_triangle_angles_le

end PlanarMinimax
