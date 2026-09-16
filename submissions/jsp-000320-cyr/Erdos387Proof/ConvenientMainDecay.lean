import Erdos387Proof.MediumBrunMainTermDecay

/-! The convenient zero-mode normalization. The extra rough factor is
paid explicitly; no logarithmic dyadic-partition cost is introduced. -/

set_option autoImplicit false
namespace Erdos387Proof.ConvenientMainDecay
open Erdos387 Erdos387.CoverBPZ MediumSieveEuler MediumMainTermDecay
open MediumBrunMainTermDecay Filter
open scoped BigOperators Topology

noncomputable def plainAlpha (k p : ℕ) : ℝ := (k : ℝ)/p

theorem plainAlpha_le_alpha {k p : ℕ} (hp : p.Prime) (hkp : 4*k ≤ p) :
    plainAlpha k p ≤ alpha k p := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hkpR : (k : ℝ)≤p := by exact_mod_cast (show k≤p by omega)
  unfold plainAlpha alpha
  field_simp
  nlinarith

theorem plainAlpha_bounds {k z p : ℕ} (hp : p ∈ windowPrimes k z) :
    0 ≤ plainAlpha k p ∧ plainAlpha k p ≤ 1/2 := by
  have hm := mem_windowPrimes.mp hp
  exact ⟨by unfold plainAlpha; positivity,
    (plainAlpha_le_alpha hm.1 hm.2.1).trans (alpha_bounds hm.1 hm.2.1).2⟩

theorem plainBrun_nonneg (k z : ℕ) {L : ℕ} (hL : Even L) :
    0 ≤ brunSubsetSum (windowPrimes k z) (plainAlpha k) L := by
  have h := BrunTruncation.brunSubsetSum_bounds_of_even (windowPrimes k z)
    (plainAlpha k) hL (fun _ hp => plainAlpha_bounds hp)
  exact h.1.le.trans h.2.1

theorem eventually_plainBrun_le_density {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      brunSubsetSum (windowPrimes S.k (SubpowerScale.z N S.k)) (plainAlpha S.k) (2*N) ≤
        (2*(2 : ℝ)^(4*S.k))*refinedDensity S (SubpowerScale.z N S.k) := by
  have hk : 0<S.k := by have := S.hk3; omega
  filter_upwards [eventually_relativeTailFactor_le_one hk] with N htail
  let P := windowPrimes S.k (SubpowerScale.z N S.k)
  have h := BrunTruncation.brunSubsetSum_bounds_of_even P (plainAlpha S.k)
    (even_two_mul N) (fun _ hp => plainAlpha_bounds hp)
  have hsum : (∑ p ∈ P, plainAlpha S.k p) ≤ ∑ p ∈ P, alpha S.k p := by
    apply Finset.sum_le_sum
    intro p hp
    have hm := mem_windowPrimes.mp hp
    exact plainAlpha_le_alpha hm.1 hm.2.1
  have htail' : ((2 : ℝ)^(2*N+1))⁻¹ * Real.exp (4*∑ p ∈ P, plainAlpha S.k p) ≤ 1 := by
    apply le_trans _ htail
    unfold relativeTailFactor
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have htwo : brunSubsetSum P (plainAlpha S.k) (2*N) ≤ 2*finiteEulerProduct P (plainAlpha S.k) :=
    h.2.2.trans (by nlinarith [mul_nonneg h.1.le (sub_nonneg.mpr htail')])
  have hshift := window_shift_euler_le_refined S (SubpowerScale.z N S.k)
  change finiteEulerProduct P (plainAlpha S.k) ≤ _ at hshift
  exact htwo.trans (by nlinarith)

theorem exists_roughMass_pow_div_log_le_inv {k : ℕ} (hk : 0<k) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 0<N →
      roughReciprocalMass (SubpowerScale.z N k) (SubpowerScale.X N k)^(k+1) /
        Real.log (SubpowerScale.z N k : ℝ) ≤ C/(N : ℝ) := by
  obtain ⟨A,hA,hmass⟩ := exists_full_roughMass_quadratic_bound hk
  let C := A^(k+1)/((BPZScale.xExp k : ℝ)*Real.log 2)
  have hx : (0 : ℝ)<BPZScale.xExp k := by unfold BPZScale.xExp; positivity
  have hl2 : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N hN
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hlog : 0<Real.log (SubpowerScale.z N k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<SubpowerScale.z N k from
      lt_of_lt_of_le (by omega) (SubpowerScale.two_le_z hN hk)))
  have hp := pow_le_pow_left₀
    (show 0≤roughReciprocalMass (SubpowerScale.z N k) (SubpowerScale.X N k) from by
      unfold roughReciprocalMass; positivity) (hmass N hN) (k+1)
  apply (div_le_div_of_nonneg_right hp hlog.le).trans_eq
  have he : ((N : ℝ)^2)^(k+1)*(N : ℝ)=(N : ℝ)^(2*k+3) := by
    rw [← pow_mul, ← pow_succ]
    congr 1
  rw [mul_pow, SubpowerScale.log_z_eq]
  unfold SubpowerScale.roughPower
  push_cast
  rw [← he]
  dsimp [C]
  field_simp

noncomputable def normalizedMainFactor {B K : ℕ}
    (S : BPZSection6Input B K) (N : ℕ) : ℝ :=
  (brunSubsetSum (windowPrimes S.k (SubpowerScale.z N S.k)) (plainAlpha S.k) (2*N) *
    (roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^(S.k+1) /
      Real.log (SubpowerScale.z N S.k : ℝ))) /
        refinedDensity S (SubpowerScale.z N S.k)

theorem tendsto_normalizedMainFactor_zero {B K : ℕ} (S : BPZSection6Input B K) :
    Tendsto (normalizedMainFactor S) atTop (𝓝 0) := by
  have hk : 0<S.k := by have := S.hk3; omega
  obtain ⟨C,hC,hbound⟩ := exists_roughMass_pow_div_log_le_inv hk
  have hlim : Tendsto (fun N : ℕ => ((2*(2 : ℝ)^(4*S.k))*C)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    unfold normalizedMainFactor
    have hbr := plainBrun_nonneg S.k (SubpowerScale.z N S.k) (even_two_mul N)
    have hl : 0<Real.log (SubpowerScale.z N S.k : ℝ) := Real.log_pos (by
      exact_mod_cast (show 1<SubpowerScale.z N S.k from lt_of_lt_of_le (by omega)
        (SubpowerScale.two_le_z (by omega) hk)))
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    unfold roughReciprocalMass
    positivity
  · filter_upwards [eventually_plainBrun_le_density S,eventually_ge_atTop (1 : ℕ)] with N hb hN
    have hm := hbound N (by omega)
    have hV := refinedDensity_pos S (SubpowerScale.z N S.k)
    have hl : 0<Real.log (SubpowerScale.z N S.k : ℝ) := Real.log_pos (by
      exact_mod_cast (show 1<SubpowerScale.z N S.k from lt_of_lt_of_le (by omega)
        (SubpowerScale.two_le_z (by omega) hk)))
    have hr : 0≤roughReciprocalMass (SubpowerScale.z N S.k) (SubpowerScale.X N S.k)^(S.k+1) /
        Real.log (SubpowerScale.z N S.k : ℝ) := by unfold roughReciprocalMass; positivity
    unfold normalizedMainFactor
    apply (div_le_iff₀ hV).mpr
    have hmul := mul_le_mul hb hm hr (by positivity :
      0≤(2*(2 : ℝ)^(4*S.k))*refinedDensity S (SubpowerScale.z N S.k))
    convert hmul using 1
    ring

end Erdos387Proof.ConvenientMainDecay
