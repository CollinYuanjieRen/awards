import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace ReciprocalSquares

/-- A finite product of small perturbations of one stays in the right half-plane.
This controls the centered characteristic function without choosing arguments. -/
theorem prod_one_add_re_pos {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∑ i ∈ s, ‖f i‖ < Real.log 2) :
    0 < (∏ i ∈ s, (1 + f i)).re := by
  have hexp : Real.exp (∑ i ∈ s, ‖f i‖) < 2 := by
    calc
      Real.exp (∑ i ∈ s, ‖f i‖) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h
      _ = 2 := Real.exp_log (by norm_num)
  have hnorm : ‖∏ i ∈ s, (1 + f i) - 1‖ < 1 :=
    lt_of_le_of_lt (s.norm_prod_one_add_sub_one_le f) (by linarith)
  have habs := Complex.abs_re_le_norm (∏ i ∈ s, (1 + f i) - 1)
  have hneg := neg_le_abs ((∏ i ∈ s, (1 + f i) - 1).re)
  simp only [Complex.sub_re, Complex.one_re] at habs hneg
  linarith

/-- Positive real parts allow normalization of each factor. A small total
imaginary-to-real ratio keeps the entire product in the right half-plane. -/
theorem prod_re_pos_of_sum_ratio_lt {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hre : ∀ i ∈ s, 0 < (z i).re)
    (hsmall : ∑ i ∈ s, |(z i).im| / (z i).re < Real.log 2) :
    0 < (∏ i ∈ s, z i).re := by
  let g : ι → ℂ := fun i => (((z i).im / (z i).re : ℝ) : ℂ) * Complex.I
  have hg : ∑ i ∈ s, ‖g i‖ < Real.log 2 := by
    convert hsmall using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, abs_of_pos (hre i hi)]
  have hp := prod_one_add_re_pos s g hg
  have hfactor : ∏ i ∈ s, z i =
      ((∏ i ∈ s, (z i).re : ℝ) : ℂ) * ∏ i ∈ s, (1 + g i) := by
    calc
      ∏ i ∈ s, z i = ∏ i ∈ s, (((z i).re : ℂ) * (1 + g i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply Complex.ext <;> simp [g, Complex.mul_re, Complex.mul_im]
        field_simp [ne_of_gt (hre i hi)]
      _ = _ := by rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [hfactor, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (Finset.prod_pos hre) hp

end ReciprocalSquares
