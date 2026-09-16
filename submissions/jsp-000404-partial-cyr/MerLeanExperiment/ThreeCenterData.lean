import MerLeanExperiment.ThreeCenterFrame
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Dependent finite data extracted from the explicit three-center frame.
-/

namespace PlanarMinimax

noncomputable def threeDepth (m : ℕ) : Fin 3 → ℕ :=
  fun t ↦ Fin.cases (m - 1) (Fin.cases (m - 1) (fun _ ↦ m - 2)) t

noncomputable def threeInternalAngle (m : ℕ) :
    (t : Fin 3) → Fin (threeDepth m t) → ℝ :=
  fun t r ↦ ((r : ℝ) + if t = 1 then 1 else 3 / 2) * threeDelta m

noncomputable def threeInternalVector (m : ℕ) (t : Fin 3)
    (r : Fin (threeDepth m t)) : Plane :=
  unitDirection (threeInternalAngle m t r)

noncomputable def threeSignedInternal (σ : Bool) (m : ℕ) (t : Fin 3)
    (r : Fin (threeDepth m t)) : Plane :=
  if σ then threeInternalVector m t r else -threeInternalVector m t r

theorem threeInternalVector_ne_zero (m : ℕ) (t : Fin 3)
    (r : Fin (threeDepth m t)) : threeInternalVector m t r ≠ 0 := by
  exact unitDirection_ne_zero _

theorem threeSignedInternal_eq (σ : Bool) (m : ℕ) (t : Fin 3)
    (r : Fin (threeDepth m t)) :
    threeSignedInternal σ m t r = signedDirection σ (threeInternalAngle m t r) := by
  rfl

theorem threeInternal_within_le {m : ℕ} (hm : 2 ≤ m) (t : Fin 3)
    {r s : Fin (threeDepth m t)} (hrs : r ≠ s) (σ τ : Bool) :
    InnerProductGeometry.angle (threeSignedInternal σ m t r)
        (threeSignedInternal τ m t s) ≤ Real.pi - threeDelta m := by
  fin_cases t
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, angleA, Fin.cases_zero, Fin.cases_succ] using
        signed_angleA_le hm hrs σ τ
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, angleB, Fin.cases_zero, Fin.cases_succ] using
        signed_angleB_le hm hrs σ τ
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, angleC, Fin.cases_zero, Fin.cases_succ] using
        signed_angleC_le hm hrs σ τ

theorem threeInternal_external_le {m : ℕ} (hm : 2 ≤ m) (t s : Fin 3)
    (hts : t ≠ s) (r : Fin (threeDepth m t)) (σ : Bool) :
    InnerProductGeometry.angle (threeSignedInternal σ m t r)
        (threeCenter m s - threeCenter m t) ≤ Real.pi - threeDelta m := by
  fin_cases t <;> fin_cases s
  · exact (hts rfl).elim
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleA, Fin.cases_zero, Fin.cases_succ] using
        (angleA_center_displacements_le hm r σ).1
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleA, Fin.cases_zero, Fin.cases_succ] using
        (angleA_center_displacements_le hm r σ).2
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleB, Fin.cases_zero, Fin.cases_succ] using
        (angleB_center_displacements_le hm r σ).1
  · exact (hts rfl).elim
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleB, Fin.cases_zero, Fin.cases_succ] using
        (angleB_center_displacements_le hm r σ).2
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleC, Fin.cases_zero, Fin.cases_succ] using
        (angleC_center_displacements_le hm r σ).1
  · simpa [threeSignedInternal, threeInternalVector, threeInternalAngle, threeDepth,
      signedDirection, threeCenter, angleC, Fin.cases_zero, Fin.cases_succ] using
        (angleC_center_displacements_le hm r σ).2
  · exact (hts rfl).elim

theorem threeCenter_triples_le {m : ℕ} (hm : 2 ≤ m) (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    EuclideanGeometry.angle (threeCenter m i) (threeCenter m j) (threeCenter m k) ≤
      Real.pi - threeDelta m := by
  have hA := (center_triangle_angles_le hm).1
  have hB := (center_triangle_angles_le hm).2.1
  have hC := (center_triangle_angles_le hm).2.2
  have hA' : EuclideanGeometry.angle (centerC m) centerA (centerB m) ≤
      Real.pi - threeDelta m := by
    rw [EuclideanGeometry.angle_comm]
    exact hA
  have hB' : EuclideanGeometry.angle (centerC m) (centerB m) centerA ≤
      Real.pi - threeDelta m := by
    rw [EuclideanGeometry.angle_comm]
    exact hB
  have hC' : EuclideanGeometry.angle (centerB m) (centerC m) centerA ≤
      Real.pi - threeDelta m := by
    rw [EuclideanGeometry.angle_comm]
    exact hC
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [threeCenter]

theorem threeDepth_cardinality {m : ℕ} (hm : 2 ≤ m) :
    ∑ t : Fin 3, 2 ^ threeDepth m t = 2 ^ m + 2 ^ (m - 2) := by
  rw [Fin.sum_univ_three]
  change 2 ^ (m - 1) + 2 ^ (m - 1) + 2 ^ (m - 2) = _
  have hm1 : m - 1 = (m - 2) + 1 := by omega
  have hm2 : m = (m - 2) + 2 := by omega
  have hp1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    calc
      2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by rw [hm1]
      _ = 2 * 2 ^ (m - 2) := by rw [pow_succ]; omega
  have hp2 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    calc
      2 ^ m = 2 ^ ((m - 2) + 2) := congrArg (fun n ↦ 2 ^ n) hm2
      _ = 4 * 2 ^ (m - 2) := by rw [pow_succ, pow_succ]; omega
  rw [hp1, hp2]
  ring

theorem threeCap_formula (m : ℕ) :
    Real.pi - threeDelta m =
      Real.pi * (1 - 2 / (2 * (m : ℝ) + 1)) := by
  unfold threeDelta
  ring

#print axioms threeInternalVector_ne_zero
#print axioms threeInternal_within_le
#print axioms threeInternal_external_le
#print axioms threeCenter_triples_le
#print axioms threeDepth_cardinality
#print axioms threeCap_formula

end PlanarMinimax
