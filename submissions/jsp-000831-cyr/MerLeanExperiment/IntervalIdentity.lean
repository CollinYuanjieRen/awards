import MerLeanExperiment.Basic
import Mathlib.Tactic

/-! Exact fractional-part identity for a half-open interval, including endpoints. -/

namespace Kesten

/-- Subtracting a real number before or after taking a fractional part gives the same
fractional part. Adapted from plby's `ErdosProblems/Erdos998.lean` (Apache-2.0;
formal authors Codex and GPT-5.6 Sol). -/
private lemma fract_sub_eq_fract_fract_sub (x a : ℝ) :
    Int.fract (x - a) = Int.fract (Int.fract x - a) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x⌋, ?_⟩
  rw [Int.fract]
  ring

/-- The centered indicator of `[u, v)` is the coboundary obtained by translating the
fractional-part function. -/
theorem indicator_sub_length_eq_fract_sub (x u v : ℝ) (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ 1) :
    (if u ≤ Int.fract x ∧ Int.fract x < v then (1 : ℝ) else 0) - (v - u) =
      Int.fract (x - v) - Int.fract (x - u) := by
  have hy0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hy1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [fract_sub_eq_fract_fract_sub x v, fract_sub_eq_fract_fract_sub x u]
  by_cases hvy : v ≤ Int.fract x
  · have huy : u ≤ Int.fract x := le_trans huv.le hvy
    have hfv : Int.fract (Int.fract x - v) = Int.fract x - v :=
      Int.fract_eq_self.mpr ⟨sub_nonneg.mpr hvy, by linarith⟩
    have hfu : Int.fract (Int.fract x - u) = Int.fract x - u :=
      Int.fract_eq_self.mpr ⟨sub_nonneg.mpr huy, by linarith⟩
    simp [huy, not_lt_of_ge hvy, hfv, hfu]
  · have hyv : Int.fract x < v := lt_of_not_ge hvy
    by_cases huy : u ≤ Int.fract x
    · have hfv : Int.fract (Int.fract x - v) = Int.fract x - v + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, -1, ?_⟩
        norm_num
      have hfu : Int.fract (Int.fract x - u) = Int.fract x - u :=
        Int.fract_eq_self.mpr ⟨sub_nonneg.mpr huy, by linarith⟩
      simp [huy, hyv, hfv, hfu]
      ring
    · have hyu : Int.fract x < u := lt_of_not_ge huy
      have hfv : Int.fract (Int.fract x - v) = Int.fract x - v + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, -1, ?_⟩
        norm_num
      have hfu : Int.fract (Int.fract x - u) = Int.fract x - u + 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, -1, ?_⟩
        norm_num
      simp [huy, hfv, hfu]

end Kesten
