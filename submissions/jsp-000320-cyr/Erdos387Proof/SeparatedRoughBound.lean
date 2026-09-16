import Erdos387Proof.SeparatedWeightedPhase
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Uniform size of the actual whole-interval rough exponential-sum bound.
The square-root saving is explicit and every dyadic/logarithmic factor is
retained in a fixed cubic logarithmic loss. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedRoughBound
open Erdos387 Erdos387.CoverBPZ SeparatedWeightedPhase

noncomputable def boundConstant : ℝ :=
  4+6*(2/Real.log 2+1)*(1+Real.log 5)^2

theorem boundConstant_pos : 0<boundConstant := by
  have h2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0<Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  unfold boundConstant
  positivity

theorem log_linear_le {X u : ℝ} (hX : 1≤X) (hu : 0<u) (huX : u≤5*X) :
    1+Real.log u≤(1+Real.log 5)*(1+Real.log X) := by
  have hlogX : 0≤Real.log X := Real.log_nonneg hX
  have hlog5 : 0≤Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hu' := Real.log_le_log hu huX
  rw [Real.log_mul (by norm_num) (by linarith : X≠0)] at hu'
  nlinarith [mul_nonneg hlog5 hlogX]

theorem log2_add_one_le (X : ℕ) :
    ((Nat.log2 X+1 : ℕ) : ℝ)≤(1/Real.log 2+1)*(1+Real.log (X : ℝ)) := by
  have h := Real.log2_le_logb X
  have h2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0≤Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hd : 0≤1/Real.log (2 : ℝ) := by positivity
  simp only [Real.logb] at h
  have he : Real.log (X : ℝ)/Real.log 2=(1/Real.log 2)*Real.log X := by ring
  rw [he] at h
  push_cast
  nlinarith

theorem roughBound_le {k t Q X : ℕ} (ht : 1≤t) (hX : 1≤X)
    (hyX : BPZScale.y t k≤X) (hQX : Q≤2*X) :
    roughBound k t Q≤boundConstant*((Q : ℝ)/Real.sqrt (t : ℝ))*
      (1+Real.log (X : ℝ))^3 := by
  let y := BPZScale.y t k
  let L : ℝ := 1+Real.log (X : ℝ)
  let J : ℝ := 1+Real.log 5
  let D : ℝ := 2/Real.log 2+1
  have htR : (1 : ℝ)≤t := by exact_mod_cast ht
  have ht0 : (0 : ℝ)<t := by linarith
  have hXr : (1 : ℝ)≤X := by exact_mod_cast hX
  have hy1 : 1≤y := one_le_pow₀ ht
  have hyr : (0 : ℝ)<y := by exact_mod_cast hy1
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogX : 0≤Real.log (X : ℝ) := Real.log_nonneg hXr
  have hL : 1≤L := by dsimp [L]; linarith
  have hJ : 0≤J := by dsimp [J]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hylog : 1+Real.log (y : ℝ)≤L := by
    dsimp [L]
    have hyXr : (y : ℝ)≤(X : ℝ) := by exact_mod_cast hyX
    exact add_le_add_right (Real.log_le_log hyr hyXr) 1
  have hlogy : (1+Real.log (2*(y : ℝ)+1))≤J*L := by
    apply log_linear_le hXr (by positivity)
    have hy : (y : ℝ)≤X := by exact_mod_cast hyX
    nlinarith
  have hlogQ : (1+Real.log (2*(Q : ℝ)+1))≤J*L := by
    apply log_linear_le hXr (by positivity)
    have hq : (Q : ℝ)≤2*(X : ℝ) := by exact_mod_cast hQX
    nlinarith
  have hdyadic : ((Nat.log2 (y^2)+1 : ℕ) : ℝ)≤D*L := by
    have h := Real.log2_le_logb (y^2)
    simp only [Real.logb,Nat.cast_pow,Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hyl : Real.log (y : ℝ)≤Real.log (X : ℝ) := by linarith
    have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyl (by norm_num : (0 : ℝ)≤2)) hlog2.le
    push_cast
    dsimp [D,L]
    have hxdiv : 0≤2/Real.log (2 : ℝ) := by positivity
    have he : 2*Real.log (X : ℝ)/Real.log 2=(2/Real.log 2)*Real.log X := by ring
    rw [he] at hdiv
    nlinarith
  have hsqrt : Real.sqrt (t : ℝ)≤t := (Real.sqrt_le_self_iff).mpr (Or.inr htR)
  have hratio : (Q : ℝ)/t≤(Q : ℝ)/Real.sqrt (t : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.sqrt_pos.mpr ht0) hsqrt
  have hroot : Real.sqrt (6*(Q : ℝ)^2/(t : ℝ))≤3*((Q : ℝ)/Real.sqrt (t : ℝ)) := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ)≤6),Real.sqrt_sq (Nat.cast_nonneg Q)]
    have hs : Real.sqrt (6 : ℝ)≤3 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    calc
      _ ≤ (3*(Q : ℝ))/Real.sqrt (t : ℝ) := by gcongr
      _ = _ := by ring
  have hL3 : L≤L^3 := by nlinarith [sq_nonneg (L-1)]
  have hly0 : 0≤1+Real.log (2*(y : ℝ)+1) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [show (0 : ℝ)≤y by positivity]))
  have hlq0 : 0≤1+Real.log (2*(Q : ℝ)+1) :=
    add_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [show (0 : ℝ)≤Q by positivity]))
  unfold roughBound
  change 4*(Q : ℝ)/(t : ℝ)*(1+Real.log (y : ℝ))+
    ((Nat.log2 (y^2)+1 : ℕ) : ℝ)*(1+Real.log (2*(Q : ℝ)+1))*
      (1+Real.log (2*(y : ℝ)+1))*(2*Real.sqrt (6*(Q : ℝ)^2/(t : ℝ)))≤_
  calc
    _ ≤ 4*((Q : ℝ)/Real.sqrt (t : ℝ))*L+
        (D*L)*(J*L)*(J*L)*(2*(3*((Q : ℝ)/Real.sqrt (t : ℝ)))) := by
      apply add_le_add
      · rw [mul_div_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (by norm_num)) hylog
          (by positivity) (by positivity)
      · gcongr
    _ ≤ 4*((Q : ℝ)/Real.sqrt (t : ℝ))*L^3+
        (D*L)*(J*L)*(J*L)*(2*(3*((Q : ℝ)/Real.sqrt (t : ℝ)))) := by gcongr
    _ = _ := by dsimp [boundConstant,D,J,L]; ring

end Erdos387Proof.SeparatedRoughBound
