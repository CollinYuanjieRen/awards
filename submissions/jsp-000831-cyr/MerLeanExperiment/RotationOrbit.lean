import MerLeanExperiment.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

/-! Irrational circle rotation: iteration, Haar preservation, and dense forward orbit. -/

namespace Kesten

open AddCircle MeasureTheory Set

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Iterating a circle translation adds the corresponding natural multiple. -/
theorem rotation_iterate_apply (a x : AddCircle (1 : ℝ)) (n : ℕ) :
    ((fun y : AddCircle (1 : ℝ) ↦ y + a)^[n]) x = x + n • a := by
  exact add_right_iterate_apply a x

/-- Translation on the unit circle preserves normalized Haar measure. -/
theorem measurePreserving_rotation (a : AddCircle (1 : ℝ)) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) ↦ x + a) haarAddCircle haarAddCircle :=
  measurePreserving_add_right haarAddCircle a

/-- The forward orbit of an irrational rotation, started at the rotation point, is dense. -/
theorem denseRange_rotation (α : ℝ) (hα : Irrational α) :
    DenseRange (fun j : ℕ ↦
      ((fun x : AddCircle (1 : ℝ) ↦ x + (α : AddCircle (1 : ℝ)))^[j])
        (α : AddCircle (1 : ℝ))) := by
  let a : AddCircle (1 : ℝ) := α
  have hz : DenseRange (fun j : ℤ ↦ j • a) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa [a] using hα
  have hn : DenseRange (fun j : ℕ ↦ j • a) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have hc : Continuous (fun x : AddCircle (1 : ℝ) ↦ a + x) := by
    fun_prop
  have hadd : DenseRange (fun j : ℕ ↦ a + j • a) := by
    change DenseRange ((fun x : AddCircle (1 : ℝ) ↦ a + x) ∘ fun j : ℕ ↦ j • a)
    exact (add_left_surjective a).denseRange.comp hn hc
  simpa only [rotation_iterate_apply, a] using hadd

end Kesten
