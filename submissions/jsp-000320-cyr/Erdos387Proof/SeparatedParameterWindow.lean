import Erdos387Proof.SeparatedPartialFourier
import Erdos387Proof.SeparatedFrequencyWindow

/-! All finite analytic side conditions for the separated range hold on
the original subpower scale, with one threshold chosen before certificates. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedParameterWindow
open Erdos387 Erdos387.CoverBPZ MediumFourierTailDecay Filter

 theorem base_le_y (N k : ℕ) : SubpowerScale.base N k≤SubpowerScale.y N k := by
  have hb : 1≤SubpowerScale.base N k := by unfold SubpowerScale.base; exact one_le_pow₀ (by norm_num)
  have he : 1≤BPZScale.yExp k := by
    unfold BPZScale.yExp
    have h3 : 1≤3^k := one_le_pow₀ (by norm_num)
    omega
  simpa only [SubpowerScale.y,BPZScale.y,pow_one] using Nat.pow_le_pow_right hb he

theorem y_le_X (N : ℕ) {k : ℕ} (hk : 0<k) : SubpowerScale.y N k≤SubpowerScale.X N k := by
  have hb : 1≤SubpowerScale.base N k := by unfold SubpowerScale.base; exact one_le_pow₀ (by norm_num)
  have he : BPZScale.yExp k≤BPZScale.xExp k := by
    unfold BPZScale.yExp BPZScale.xExp
    have hkpow : 1≤k^100 := one_le_pow₀ hk
    exact le_mul_of_one_le_right (Nat.zero_le _) hkpow
  exact Nat.pow_le_pow_right hb he

theorem eventually_parameters {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      0<N ∧ 2*S.k≤SubpowerScale.z N S.k ∧ S.k≤SubpowerScale.X N S.k ∧
      SubpowerScale.z N S.k≤SubpowerScale.y N S.k ∧
      6*2^S.k≤SubpowerScale.base N S.k ∧ refinementModulus S≤SubpowerScale.base N S.k ∧
      SubpowerScale.z N S.k^(2*N)≤SubpowerScale.base N S.k ∧
      2≤height N S.k ∧ height N S.k^2≤SubpowerScale.base N S.k := by
  have hk : 0<S.k := by have := S.hk3; omega
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    SubpowerScale.eventually_const_le_z hk (2*S.k),
    SubpowerScale.eventually_const_le_X hk S.k,
    eventually_const_le_base S.k (6*2^S.k),
    eventually_const_le_base S.k (refinementModulus S),
    eventually_height_pow_mul_support_le_base S.k 0 2,
    eventually_height_pow_mul_support_le_base S.k 2 0] with N hN hz hkX ht hM hg hH
  simp only [pow_zero,one_mul,zero_mul,mul_one] at hg hH
  have hzG : SubpowerScale.z N S.k≤SubpowerScale.z N S.k^(2*N) := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (SubpowerScale.z_pos N S.k) (by omega : 1≤2*N)
  exact ⟨by omega,hz,hkX,hzG.trans (hg.trans (base_le_y N S.k)),ht,hM,hg,
    SeparatedFrequencyWindow.height_two_le N S.k (by omega) hk,hH⟩

end Erdos387Proof.SeparatedParameterWindow
