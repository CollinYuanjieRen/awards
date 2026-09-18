import MerLeanExperiment.ExponentialTail

/-!
# Elementary finite-exponential bounds for exterior overconvergence

These exact identities are the finite-sum and differentiation interfaces used
when formalizing Luo--Yang--Zhu Proposition 3.3.
-/
open Finset
namespace Erdos973

theorem norm_truncatedExp_le_exp_norm (m : ℕ) (u : ℂ) :
    ‖truncatedExp m u‖ ≤ Real.exp ‖u‖ := by
  calc
    ‖truncatedExp m u‖ ≤ ∑ j ∈ range (m + 1), ‖u ^ j / (j.factorial : ℂ)‖ := by
      rw [truncatedExp]
      exact norm_sum_le _ _
    _ = ∑ j ∈ range (m + 1), ‖u‖ ^ j / (j.factorial : ℝ) := by
      apply sum_congr rfl
      intro j hj
      simp
    _ ≤ ∑' j : ℕ, ‖u‖ ^ j / (j.factorial : ℝ) := by
      exact (NormedSpace.expSeries_div_hasSum_exp ‖u‖).summable.sum_le_tsum
        (range (m + 1)) (fun j hj => by positivity)
    _ = Real.exp ‖u‖ := by
      rw [Real.exp_eq_exp_ℝ]
      exact (NormedSpace.expSeries_div_hasSum_exp ‖u‖).tsum_eq

end Erdos973

open Finset
namespace Erdos973

theorem truncatedExp_succ (m : ℕ) (u : ℂ) :
    truncatedExp (m + 1) u = truncatedExp m u + u ^ (m + 1) / ((m + 1).factorial : ℂ) := by
  simp [truncatedExp, sum_range_succ, Nat.add_assoc]

theorem truncatedExp_eq_pred_add (m : ℕ) (u : ℂ) :
    truncatedExp m u = truncatedExpPred m u + u ^ m / (m.factorial : ℂ) := by
  cases m with
  | zero => simp [truncatedExp, truncatedExpPred]
  | succ m => simp [truncatedExpPred, truncatedExp_succ]

theorem hasDerivAt_truncatedExp (m : ℕ) (u : ℂ) :
    HasDerivAt (truncatedExp m) (truncatedExpPred m u) u := by
  induction m with
  | zero =>
      have hfun : truncatedExp 0 = fun _ : ℂ => 1 := by
        funext v
        simp [truncatedExp]
      have hpred : truncatedExpPred 0 u = 0 := rfl
      rw [hfun, hpred]
      exact hasDerivAt_const u 1
  | succ m ih =>
      have hterm0 := (hasDerivAt_pow (m + 1) u).div_const ((m + 1).factorial : ℂ)
      have hterm : HasDerivAt
          (fun v : ℂ => v ^ (m + 1) / ((m + 1).factorial : ℂ))
          (u ^ m / (m.factorial : ℂ)) u := by
        refine hterm0.congr_deriv ?_
        simp only [Nat.add_sub_cancel]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
      have hsum := ih.fun_add hterm
      have hfun : truncatedExp (m + 1) =
          fun v => truncatedExp m v + v ^ (m + 1) / ((m + 1).factorial : ℂ) := by
        funext v
        rw [truncatedExp_succ]
      have hder : truncatedExp m u =
          truncatedExpPred m u + u ^ m / (m.factorial : ℂ) :=
        truncatedExp_eq_pred_add m u
      have hpredsucc : truncatedExpPred (m + 1) u = truncatedExp m u := by
        simp [truncatedExpPred]
      rw [hfun, hpredsucc, hder]
      exact hsum

end Erdos973

