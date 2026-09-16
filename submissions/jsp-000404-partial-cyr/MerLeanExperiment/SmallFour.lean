import MerLeanExperiment.CapSemantics
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-!
The exact four-point case of the ordinary planar minimax-angle problem.
-/

namespace PlanarMinimax

open scoped InnerProductSpace

/-- The four vertices of the unit square. -/
def squarePoint : Fin 4 → Plane :=
  ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/-- The indexed vertices of the unit square are distinct. -/
theorem squarePoint_injective : Function.Injective squarePoint := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [squarePoint]

/-- Every centered scalar product among vertices of the unit square is nonnegative. -/
theorem squarePoint_inner_nonneg (i j k : Fin 4) :
    0 ≤ ⟪squarePoint i - squarePoint j, squarePoint k - squarePoint j⟫_ℝ := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [squarePoint, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two]

/-- The unit square realizes the cap `π / 2`. -/
theorem square_realizableCap : RealizableCap 4 (Real.pi / 2) := by
  refine ⟨squarePoint, squarePoint_injective, ?_⟩
  intro i j k _ _ _
  unfold EuclideanGeometry.angle InnerProductGeometry.angle
  rw [Real.arccos_le_pi_div_two]
  exact div_nonneg (squarePoint_inner_nonneg i j k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A nontrivial nonnegative combination of three inward vectors cannot vanish. -/
theorem singleton_combination_ne_zero {u v w : Plane} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : 0 < a + b + c)
    (hu : 0 < ⟪u, u⟫_ℝ) (hv : 0 < ⟪v, u⟫_ℝ) (hw : 0 < ⟪w, u⟫_ℝ) :
    a • u + b • v + c • w ≠ 0 := by
  intro hzero
  have hinner := congrArg (fun x : Plane ↦ ⟪x, u⟫_ℝ) hzero
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hinner
  by_cases ha_pos : 0 < a
  · nlinarith [mul_pos ha_pos hu, mul_nonneg hb hv.le, mul_nonneg hc hw.le]
  · have ha_zero : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
    by_cases hb_pos : 0 < b
    · nlinarith [mul_pos hb_pos hv, mul_nonneg hc hw.le]
    · have hb_zero : b = 0 := le_antisymm (le_of_not_gt hb_pos) hb
      have hc_pos : 0 < c := by linarith [hsum]
      nlinarith [mul_pos hc_pos hw]

/-- The balanced two-versus-two affine relation contradicts four inward products. -/
theorem balanced_pair_relation_impossible {A B C D : Plane} {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : 0 < a + b) (hbalance : a + b = c + d)
    (hrel : a • A + b • B = c • C + d • D)
    (hA : 0 < ⟪C - A, D - A⟫_ℝ) (hB : 0 < ⟪C - B, D - B⟫_ℝ)
    (hC : 0 < ⟪A - C, B - C⟫_ℝ) (hD : 0 < ⟪A - D, B - D⟫_ℝ) : False := by
  have hidentity :
      a * ⟪C - A, D - A⟫_ℝ + b * ⟪C - B, D - B⟫_ℝ +
          c * ⟪A - C, B - C⟫_ℝ + d * ⟪A - D, B - D⟫_ℝ =
        ⟪a • A + b • B - c • C - d • D, A + B - C - D⟫_ℝ := by
    rw [show c = a + b - d by linarith [hbalance]]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hzero : a • A + b • B - c • C - d • D = 0 := by
    rw [hrel]
    module
  rw [hzero, inner_zero_left] at hidentity
  by_cases ha_pos : 0 < a
  · nlinarith [mul_pos ha_pos hA, mul_nonneg hb hB.le,
      mul_nonneg hc hC.le, mul_nonneg hd hD.le]
  · have hb_pos : 0 < b := by nlinarith [hsum]
    nlinarith [mul_nonneg ha hA.le, mul_pos hb_pos hB,
      mul_nonneg hc hC.le, mul_nonneg hd hD.le]

/-- One positive coefficient cannot balance three nonpositive coefficients at acute points. -/
theorem one_positive_relation_impossible {A B C D : Plane} {a b c d : ℝ}
    (ha : 0 < a) (hb : b ≤ 0) (hc : c ≤ 0) (hd : d ≤ 0)
    (hsum : a + b + c + d = 0)
    (hrel : a • A + b • B + c • C + d • D = 0)
    (hB : 0 < ⟪B - A, B - A⟫_ℝ) (hC : 0 < ⟪C - A, B - A⟫_ℝ)
    (hD : 0 < ⟪D - A, B - A⟫_ℝ) : False := by
  have hvec : (-b) • (B - A) + (-c) • (C - A) + (-d) • (D - A) = 0 := by
    calc
      (-b) • (B - A) + (-c) • (C - A) + (-d) • (D - A) =
          -(b • B + c • C + d • D) + (b + c + d) • A := by module
      _ = -(a • A + b • B + c • C + d • D) := by
        rw [show b + c + d = -a by linarith [hsum]]
        module
      _ = 0 := by rw [hrel, neg_zero]
  exact singleton_combination_ne_zero (neg_nonneg.mpr hb) (neg_nonneg.mpr hc)
    (neg_nonneg.mpr hd) (by linarith [hsum]) hB hC hD hvec

/-- Two positive coefficients cannot balance two nonpositive coefficients at acute points. -/
theorem two_positive_relation_impossible {A B C D : Plane} {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : c ≤ 0) (hd : d ≤ 0)
    (hsum : a + b + c + d = 0)
    (hrel : a • A + b • B + c • C + d • D = 0)
    (hA : 0 < ⟪C - A, D - A⟫_ℝ) (hB : 0 < ⟪C - B, D - B⟫_ℝ)
    (hC : 0 < ⟪A - C, B - C⟫_ℝ) (hD : 0 < ⟪A - D, B - D⟫_ℝ) : False := by
  apply balanced_pair_relation_impossible ha.le hb.le (neg_nonneg.mpr hc) (neg_nonneg.mpr hd)
    (add_pos ha hb) (by linarith [hsum]) _ hA hB hC hD
  calc
    a • A + b • B = -(c • C + d • D) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa only [add_assoc] using hrel
    _ = (-c) • C + (-d) • D := by module

/-- An angle below `π / 2` has a positive centered scalar product. -/
theorem inner_pos_of_angle_lt {A B C : Plane} (hAB : A ≠ B) (hCB : C ≠ B)
    (hangle : EuclideanGeometry.angle A B C < Real.pi / 2) :
    0 < ⟪A - B, C - B⟫_ℝ := by
  unfold EuclideanGeometry.angle InnerProductGeometry.angle at hangle
  rw [Real.arccos_lt_pi_div_two] at hangle
  have hden : 0 < ‖A - B‖ * ‖C - B‖ := by
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hAB))
      (norm_pos_iff.mpr (sub_ne_zero.mpr hCB))
  exact (div_pos_iff_of_pos_right hden).mp hangle

set_option maxHeartbeats 1000000 in
/-- Four distinct planar points contain an angle of at least `π / 2`. -/
theorem four_guaranteed : Guaranteed 4 (Real.pi / 2) := by
  intro points hinjective
  by_contra hresult
  have hangle (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      EuclideanGeometry.angle (points i) (points j) (points k) < Real.pi / 2 := by
    exact lt_of_not_ge fun hge ↦ hresult ⟨i, j, k, hij, hjk, hik, hge⟩
  have hdot (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      0 < ⟪points i - points j, points k - points j⟫_ℝ := by
    exact inner_pos_of_angle_lt (hinjective.ne hij) (hinjective.ne hjk.symm)
      (hangle i j k hij hjk hik)
  have hself (i j : Fin 4) (hij : i ≠ j) :
      0 < ⟪points i - points j, points i - points j⟫_ℝ := by
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr (hinjective.ne hij))
  have hdependent : ¬AffineIndependent ℝ points := by
    apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ points (n := 2) (by decide)).mp
    calc
      Module.finrank ℝ (vectorSpan ℝ (Set.range points)) ≤ Module.finrank ℝ Plane := by
        simpa using
          Submodule.finrank_mono (show vectorSpan ℝ (Set.range points) ≤ ⊤ from le_top)
      _ = 2 := finrank_euclideanSpace_fin
  rw [affineIndependent_iff_of_fintype] at hdependent
  push Not at hdependent
  obtain ⟨w, hsum, hweighted, i, hi⟩ := hdependent
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hweighted
  have hsum4 : w 0 + w 1 + w 2 + w 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hrel4 :
      w 0 • points 0 + w 1 • points 1 + w 2 • points 2 + w 3 • points 3 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hweighted
  have hrel4neg :
      (-w 0) • points 0 + (-w 1) • points 1 + (-w 2) • points 2 +
          (-w 3) • points 3 = 0 := by
    calc
      (-w 0) • points 0 + (-w 1) • points 1 + (-w 2) • points 2 +
          (-w 3) • points 3 =
          -(w 0 • points 0 + w 1 • points 1 + w 2 • points 2 + w 3 • points 3) := by
            module
      _ = 0 := by rw [hrel4, neg_zero]
  by_cases h0 : 0 < w 0
  · by_cases h1 : 0 < w 1
    · by_cases h2 : 0 < w 2
      · by_cases h3 : 0 < w 3
        · nlinarith [hsum4]
        · apply one_positive_relation_impossible (A := points 3) (B := points 0)
            (C := points 1) (D := points 2) (a := -w 3) (b := -w 0)
            (c := -w 1) (d := -w 2) (by nlinarith [hsum4]) (by linarith)
            (by linarith) (by linarith) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4neg)
            (hself 0 3 (by decide)) (hdot 1 3 0 (by decide) (by decide) (by decide))
            (hdot 2 3 0 (by decide) (by decide) (by decide))
      · by_cases h3 : 0 < w 3
        · apply one_positive_relation_impossible (A := points 2) (B := points 0)
            (C := points 1) (D := points 3) (a := -w 2) (b := -w 0)
            (c := -w 1) (d := -w 3) (by nlinarith [hsum4]) (by linarith)
            (by linarith) (by linarith) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4neg)
            (hself 0 2 (by decide)) (hdot 1 2 0 (by decide) (by decide) (by decide))
            (hdot 3 2 0 (by decide) (by decide) (by decide))
        · apply two_positive_relation_impossible (A := points 0) (B := points 1)
            (C := points 2) (D := points 3) h0 h1 (le_of_not_gt h2)
            (le_of_not_gt h3) hsum4 hrel4
            (hdot 2 0 3 (by decide) (by decide) (by decide))
            (hdot 2 1 3 (by decide) (by decide) (by decide))
            (hdot 0 2 1 (by decide) (by decide) (by decide))
            (hdot 0 3 1 (by decide) (by decide) (by decide))
    · by_cases h2 : 0 < w 2
      · by_cases h3 : 0 < w 3
        · apply one_positive_relation_impossible (A := points 1) (B := points 0)
            (C := points 2) (D := points 3) (a := -w 1) (b := -w 0)
            (c := -w 2) (d := -w 3) (by nlinarith [hsum4]) (by linarith)
            (by linarith) (by linarith) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4neg)
            (hself 0 1 (by decide)) (hdot 2 1 0 (by decide) (by decide) (by decide))
            (hdot 3 1 0 (by decide) (by decide) (by decide))
        · apply two_positive_relation_impossible (A := points 0) (B := points 2)
            (C := points 1) (D := points 3) h0 h2 (le_of_not_gt h1)
            (le_of_not_gt h3) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hdot 1 0 3 (by decide) (by decide) (by decide))
            (hdot 1 2 3 (by decide) (by decide) (by decide))
            (hdot 0 1 2 (by decide) (by decide) (by decide))
            (hdot 0 3 2 (by decide) (by decide) (by decide))
      · by_cases h3 : 0 < w 3
        · apply two_positive_relation_impossible (A := points 0) (B := points 3)
            (C := points 1) (D := points 2) h0 h3 (le_of_not_gt h1)
            (le_of_not_gt h2) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hdot 1 0 2 (by decide) (by decide) (by decide))
            (hdot 1 3 2 (by decide) (by decide) (by decide))
            (hdot 0 1 3 (by decide) (by decide) (by decide))
            (hdot 0 2 3 (by decide) (by decide) (by decide))
        · exact one_positive_relation_impossible h0 (le_of_not_gt h1)
            (le_of_not_gt h2) (le_of_not_gt h3) hsum4 hrel4
            (hself 1 0 (by decide))
            (hdot 2 0 1 (by decide) (by decide) (by decide))
            (hdot 3 0 1 (by decide) (by decide) (by decide))
  · by_cases h1 : 0 < w 1
    · by_cases h2 : 0 < w 2
      · by_cases h3 : 0 < w 3
        · apply one_positive_relation_impossible (A := points 0) (B := points 1)
            (C := points 2) (D := points 3) (a := -w 0) (b := -w 1)
            (c := -w 2) (d := -w 3) (by nlinarith [hsum4]) (by linarith)
            (by linarith) (by linarith) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4neg)
            (hself 1 0 (by decide)) (hdot 2 0 1 (by decide) (by decide) (by decide))
            (hdot 3 0 1 (by decide) (by decide) (by decide))
        · apply two_positive_relation_impossible (A := points 1) (B := points 2)
            (C := points 0) (D := points 3) h1 h2 (le_of_not_gt h0)
            (le_of_not_gt h3) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hdot 0 1 3 (by decide) (by decide) (by decide))
            (hdot 0 2 3 (by decide) (by decide) (by decide))
            (hdot 1 0 2 (by decide) (by decide) (by decide))
            (hdot 1 3 2 (by decide) (by decide) (by decide))
      · by_cases h3 : 0 < w 3
        · apply two_positive_relation_impossible (A := points 1) (B := points 3)
            (C := points 0) (D := points 2) h1 h3 (le_of_not_gt h0)
            (le_of_not_gt h2) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hdot 0 1 2 (by decide) (by decide) (by decide))
            (hdot 0 3 2 (by decide) (by decide) (by decide))
            (hdot 1 0 3 (by decide) (by decide) (by decide))
            (hdot 1 2 3 (by decide) (by decide) (by decide))
        · apply one_positive_relation_impossible (A := points 1) (B := points 0)
            (C := points 2) (D := points 3) h1 (le_of_not_gt h0)
            (le_of_not_gt h2) (le_of_not_gt h3) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hself 0 1 (by decide))
            (hdot 2 1 0 (by decide) (by decide) (by decide))
            (hdot 3 1 0 (by decide) (by decide) (by decide))
    · by_cases h2 : 0 < w 2
      · by_cases h3 : 0 < w 3
        · apply two_positive_relation_impossible (A := points 2) (B := points 3)
            (C := points 0) (D := points 1) h2 h3 (le_of_not_gt h0)
            (le_of_not_gt h1) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hdot 0 2 1 (by decide) (by decide) (by decide))
            (hdot 0 3 1 (by decide) (by decide) (by decide))
            (hdot 2 0 3 (by decide) (by decide) (by decide))
            (hdot 2 1 3 (by decide) (by decide) (by decide))
        · apply one_positive_relation_impossible (A := points 2) (B := points 0)
            (C := points 1) (D := points 3) h2 (le_of_not_gt h0)
            (le_of_not_gt h1) (le_of_not_gt h3) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hself 0 2 (by decide))
            (hdot 1 2 0 (by decide) (by decide) (by decide))
            (hdot 3 2 0 (by decide) (by decide) (by decide))
      · by_cases h3 : 0 < w 3
        · apply one_positive_relation_impossible (A := points 3) (B := points 0)
            (C := points 1) (D := points 2) h3 (le_of_not_gt h0)
            (le_of_not_gt h1) (le_of_not_gt h2) (by nlinarith [hsum4])
            (by simpa only [add_assoc, add_comm, add_left_comm] using hrel4)
            (hself 0 3 (by decide))
            (hdot 1 3 0 (by decide) (by decide) (by decide))
            (hdot 2 3 0 (by decide) (by decide) (by decide))
        · have hw0 : w 0 = 0 := by nlinarith [hsum4]
          have hw1 : w 1 = 0 := by nlinarith [hsum4]
          have hw2 : w 2 = 0 := by nlinarith [hsum4]
          have hw3 : w 3 = 0 := by nlinarith [hsum4]
          fin_cases i <;> simp_all

/-- The exact ordinary minimax angle for four planar points is `π / 2`. -/
theorem minimaxAngle_four : minimaxAngle 4 = Real.pi / 2 := by
  apply le_antisymm
  · unfold minimaxAngle
    exact csInf_le (realizableCap_bddBelow (by decide)) square_realizableCap
  · exact (le_minimaxAngle_iff_guaranteed (by decide) (Real.pi / 2)).mpr
      four_guaranteed

#print axioms square_realizableCap
#print axioms four_guaranteed
#print axioms minimaxAngle_four

end PlanarMinimax
