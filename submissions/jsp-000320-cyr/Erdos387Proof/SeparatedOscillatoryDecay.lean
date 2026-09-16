import Erdos387Proof.ConvenientMomentDecay

/-! Fixed cutoff, sieve, root, reciprocal-density and polynomial losses are
absorbed by the square-root saving in the separated exponential sum. -/

set_option autoImplicit false
namespace Erdos387Proof.SeparatedOscillatoryDecay
open Erdos387 Erdos387.CoverBPZ MediumOscillatoryDecay MediumMainTermDecay Filter
open scoped Topology

theorem eventually_fourN_pow_le_base (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ)^(4*N) ≤ SubpowerScale.base N k := by
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
  have hN1 : 1≤N := by omega
  have hexp : 4*N≤SubpowerScale.scalePower N k := by
    unfold SubpowerScale.scalePower
    calc
      _ ≤ N*N := Nat.mul_le_mul_right N hN
      _ = N^2 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hN1 (by omega)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1≤2) hexp

theorem eventually_loss_div_sqrt_le_inv_pow {B K : ℕ}
    (S : BPZSection6Input B K) (a b c d : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((loss a b c d N S.k : ℝ)/refinedDensity S (SubpowerScale.z N S.k)) /
        Real.sqrt (SubpowerScale.base N S.k : ℝ) ≤ 1/(2 : ℝ)^N := by
  filter_upwards [ConvenientMomentDecay.eventually_pow_loss_div_density_le_base S a b c d 4,
    eventually_fourN_pow_le_base S.k] with N hL hN
  let A : ℝ := (loss a b c d N S.k : ℝ)/refinedDensity S (SubpowerScale.z N S.k)
  let t : ℝ := SubpowerScale.base N S.k
  have hA : 0≤A := div_nonneg (Nat.cast_nonneg _) (refinedDensity_pos S _).le
  have ht : 0<t := by dsimp [t]; unfold SubpowerScale.base; positivity
  have hpow : (A*(2 : ℝ)^N)^4 ≤ (Real.sqrt t)^4 := by
    calc
      _ = A^4*(2 : ℝ)^(4*N) := by rw [mul_pow,← pow_mul,mul_comm N 4]
      _ ≤ t*t := mul_le_mul hL hN (by positivity) ht.le
      _ = (Real.sqrt t)^4 := by nlinarith [Real.sq_sqrt ht.le]
  have hprod : A*(2 : ℝ)^N ≤ Real.sqrt t :=
    (pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg t) (by norm_num : (4 : ℕ)≠0)).mp hpow
  change A/Real.sqrt t≤_
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr ht) (by positivity : (0 : ℝ)<2^N)]
  simpa using hprod

noncomputable def normalizedEnvelope {B K : ℕ} (S : BPZSection6Input B K)
    (a b c d e f r N : ℕ) : ℝ :=
  ((loss a b c d N S.k : ℝ)/refinedDensity S (SubpowerScale.z N S.k)) /
    Real.sqrt (SubpowerScale.base N S.k : ℝ) * ((N : ℝ)+1)^f *
      (1+Real.log (SubpowerScale.X N S.k : ℝ))^e *
      roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^r

theorem tendsto_normalizedEnvelope_zero {B K : ℕ} (S : BPZSection6Input B K)
    (a b c d e f r : ℕ) :
    Tendsto (normalizedEnvelope S a b c d e f r) atTop (𝓝 0) := by
  have hk : 0<S.k := by have := S.hk3; omega
  obtain ⟨C,hC,hpoly⟩ := exists_mass_log_polynomial_bound hk
  let s := 2*S.k+5
  let D : ℝ := (2 : ℝ)^f*C^(r+e)
  have hlim : Tendsto (fun N : ℕ => D*((N : ℝ)^(s*(r+e)+f)/(2 : ℝ)^N)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt
      (s*(r+e)+f) (by norm_num : (1 : ℝ)<2)).const_mul D
  apply squeeze_zero' ?_ ?_ hlim
  · apply Filter.Eventually.of_forall
    intro N
    unfold normalizedEnvelope
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    unfold roughReciprocalMass
    positivity
  · filter_upwards [eventually_loss_div_sqrt_le_inv_pow S a b c d,
      eventually_ge_atTop (1 : ℕ)] with N hsave hN
    have hp := hpoly N (by omega)
    have hR : 0≤roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k) := by
      unfold roughReciprocalMass; positivity
    have hlog : 0≤1+Real.log (SubpowerScale.X N S.k : ℝ) := by positivity
    have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
    have hNextra : ((N : ℝ)+1)^f≤(2 : ℝ)^f*(N : ℝ)^f := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) f
    unfold normalizedEnvelope
    calc
      _ ≤ (1/(2 : ℝ)^N)*((2 : ℝ)^f*(N : ℝ)^f)*(C*(N : ℝ)^s)^e*(C*(N : ℝ)^s)^r := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul hsave hNextra (by positivity) (by positivity)
          · exact pow_le_pow_left₀ hlog hp.2 e
          · positivity
          · positivity
        · exact pow_le_pow_left₀ hR hp.1 r
        · positivity
        · positivity
      _ = _ := by
        dsimp [D]
        rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
        simp only [pow_add,mul_add]
        ring

end Erdos387Proof.SeparatedOscillatoryDecay
