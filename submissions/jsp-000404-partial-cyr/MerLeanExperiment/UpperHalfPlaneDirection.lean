import MerLeanExperiment.DirectionFrame
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

/-!
A continuous angular coordinate on the open upper half-plane.
-/

namespace PlanarMinimax

open Filter Set
open scoped Topology

/-- The angle in `(0, π)` of a vector with positive second coordinate. -/
noncomputable def upperDirectionAngle (v : Plane) : ℝ :=
  Real.arccos (v 0 / ‖v‖)

theorem upperDirection_norm_pos {v : Plane} (hy : 0 < v 1) : 0 < ‖v‖ := by
  rw [norm_pos_iff]
  intro hv
  have := congrArg (fun w : Plane ↦ w 1) hv
  simp at this
  linarith

private theorem abs_first_lt_norm {v : Plane} (hy : 0 < v 1) : |v 0| < ‖v‖ := by
  have hnorm := EuclideanSpace.real_norm_sq_eq v
  rw [Fin.sum_univ_two] at hnorm
  apply abs_lt_of_sq_lt_sq
  · nlinarith [sq_pos_of_pos hy]
  · positivity

theorem upperDirectionAngle_pos {v : Plane} (hy : 0 < v 1) :
    0 < upperDirectionAngle v := by
  rw [upperDirectionAngle, Real.arccos_pos]
  rw [div_lt_one (upperDirection_norm_pos hy)]
  exact (lt_of_le_of_lt (le_abs_self _) (abs_first_lt_norm hy))

theorem upperDirectionAngle_lt_pi {v : Plane} (hy : 0 < v 1) :
    upperDirectionAngle v < Real.pi := by
  rw [upperDirectionAngle, Real.arccos_lt_pi]
  rw [lt_div_iff₀ (upperDirection_norm_pos hy)]
  simpa using (abs_lt.mp (abs_first_lt_norm hy)).1

theorem upperDirectionAngle_mem {v : Plane} (hy : 0 < v 1) :
    upperDirectionAngle v ∈ Set.Ioo 0 Real.pi :=
  ⟨upperDirectionAngle_pos hy, upperDirectionAngle_lt_pi hy⟩

theorem upperDirectionAngle_reconstruct {v : Plane} (hy : 0 < v 1) :
    v = ‖v‖ • unitDirection (upperDirectionAngle v) := by
  have hn := upperDirection_norm_pos hy
  have habs := abs_first_lt_norm hy
  have hratio : -1 ≤ v 0 / ‖v‖ ∧ v 0 / ‖v‖ ≤ 1 := by
    constructor
    · apply (le_of_lt ?_)
      rw [lt_div_iff₀ hn]
      simpa using (abs_lt.mp habs).1
    · apply (le_of_lt ?_)
      rw [div_lt_one hn]
      exact lt_of_le_of_lt (le_abs_self _) habs
  have hcos : Real.cos (upperDirectionAngle v) = v 0 / ‖v‖ := by
    exact Real.cos_arccos hratio.1 hratio.2
  have hnorm := EuclideanSpace.real_norm_sq_eq v
  rw [Fin.sum_univ_two] at hnorm
  have hsquares : 1 - (v 0 / ‖v‖) ^ 2 = (v 1 / ‖v‖) ^ 2 := by
    field_simp
    nlinarith
  have hsin : Real.sin (upperDirectionAngle v) = v 1 / ‖v‖ := by
    rw [upperDirectionAngle, Real.sin_arccos, hsquares, Real.sqrt_sq_eq_abs,
      abs_of_pos (div_pos hy hn)]
  ext i
  fin_cases i
  · simp [unitDirection, hcos]
    field_simp
  · simp [unitDirection, hsin]
    field_simp

theorem upperDirectionAngle_unitDirection {a : ℝ} (ha : 0 < a)
    (hapi : a < Real.pi) : upperDirectionAngle (unitDirection a) = a := by
  rw [upperDirectionAngle, norm_unitDirection, div_one]
  simp only [unitDirection, Matrix.cons_val_zero]
  exact Real.arccos_cos ha.le hapi.le

theorem unitDirection_injective_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo 0 Real.pi)
    (hb : b ∈ Set.Ioo 0 Real.pi) (hab : unitDirection a = unitDirection b) : a = b := by
  have := congrArg upperDirectionAngle hab
  simpa [upperDirectionAngle_unitDirection ha.1 ha.2,
    upperDirectionAngle_unitDirection hb.1 hb.2] using this

theorem angle_eq_abs_upperDirectionAngle_sub {v w : Plane}
    (hv : 0 < v 1) (hw : 0 < w 1)
    (hdiff : |upperDirectionAngle v - upperDirectionAngle w| ≤ Real.pi) :
    InnerProductGeometry.angle v w =
      |upperDirectionAngle v - upperDirectionAngle w| := by
  calc
    InnerProductGeometry.angle v w =
        InnerProductGeometry.angle
          (‖v‖ • unitDirection (upperDirectionAngle v))
          (‖w‖ • unitDirection (upperDirectionAngle w)) := by
      rw [← upperDirectionAngle_reconstruct hv, ← upperDirectionAngle_reconstruct hw]
    _ = InnerProductGeometry.angle (unitDirection (upperDirectionAngle v))
        (unitDirection (upperDirectionAngle w)) := by
      rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (upperDirection_norm_pos hv),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (upperDirection_norm_pos hw)]
    _ = |upperDirectionAngle v - upperDirectionAngle w| :=
      angle_unitDirection _ _ hdiff

theorem exists_bool_sign_second_pos {v : Plane} (hy : v 1 ≠ 0) :
    ∃ σ : Bool, 0 < (if σ then v else -v) 1 := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · exact ⟨false, by simpa using neg_pos.mpr hneg⟩
  · exact ⟨true, by simpa using hpos⟩

theorem tendsto_upperDirectionAngle {α : Type*} {l : Filter α}
    {f : α → Plane} {v : Plane} (hf : Filter.Tendsto f l (𝓝 v)) (hv : v ≠ 0) :
    Filter.Tendsto (fun x ↦ upperDirectionAngle (f x)) l
      (𝓝 (upperDirectionAngle v)) := by
  have hcoord : Filter.Tendsto (fun x ↦ (f x) 0) l (𝓝 (v 0)) := by
    exact (PiLp.continuous_apply 2 (fun _ ↦ ℝ) 0).continuousAt.tendsto.comp hf
  have hnorm : Filter.Tendsto (fun x ↦ ‖f x‖) l (𝓝 ‖v‖) := hf.norm
  have hquot := hcoord.div hnorm (norm_ne_zero_iff.mpr hv)
  exact hquot.arccos

theorem eventually_upper_second_pos {α : Type*} {l : Filter α}
    {f : α → Plane} {v : Plane} (hf : Filter.Tendsto f l (𝓝 v)) (hy : 0 < v 1) :
    ∀ᶠ x in l, 0 < (f x) 1 := by
  have hcoord : Filter.Tendsto (fun x ↦ (f x) 1) l (𝓝 (v 1)) := by
    exact (PiLp.continuous_apply 2 (fun _ ↦ ℝ) 1).continuousAt.tendsto.comp hf
  exact hcoord.eventually (Ioi_mem_nhds hy)

#print axioms upperDirectionAngle_pos
#print axioms upperDirectionAngle_lt_pi
#print axioms upperDirection_norm_pos
#print axioms upperDirectionAngle_reconstruct
#print axioms upperDirectionAngle_unitDirection
#print axioms unitDirection_injective_Ioo
#print axioms angle_eq_abs_upperDirectionAngle_sub
#print axioms exists_bool_sign_second_pos
#print axioms tendsto_upperDirectionAngle
#print axioms eventually_upper_second_pos

end PlanarMinimax
