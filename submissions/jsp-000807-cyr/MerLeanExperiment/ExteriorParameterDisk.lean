import Mathlib

/-!
# A parameter disk outside the unit circle

This is a proof-oriented exact form of Luo--Yang--Zhu Lemma 3.2.  The chosen
`R` is the explicit maximum `‖center‖ + radius` of the norm on the closed disk;
the inequalities are the strict margins consumed by Proposition 3.3.
-/

open Metric Set
open scoped Topology

namespace Erdos973

private theorem exists_pos_of_eventually_nhds {P : ℝ → Prop}
    (h : ∀ᶠ d : ℝ in 𝓝 0, P d) : ∃ d : ℝ, 0 < d ∧ P d := by
  have hmem : {d : ℝ | P d} ∈ nhds 0 := h
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hε, hsub⟩ := hmem
  refine ⟨ε / 2, half_pos hε, hsub ?_⟩
  rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  linarith

/-- Luo--Yang--Zhu Lemma 3.2, with the closed disk represented by its center
and positive radius and with an explicit norm maximum. -/
theorem exists_exterior_parameter_disk
    {lambda : ℝ} {c : ℂ}
    (hlambda : 0 < lambda) (hc0 : 0 < ‖c‖) (hc1 : ‖c‖ < 1)
    (_hscale : lambda ≤ ‖c‖ - 1 - Real.log ‖c‖) :
    ∃ center : ℂ, ∃ radius a Q R eta : ℝ,
      0 < radius ∧ 0 < a ∧ 0 < Q ∧ 0 < R ∧ 0 < eta ∧
      R = ‖center‖ + radius ∧ R < Real.exp lambda ∧ Q < 1 ∧
      (∀ w ∈ Metric.closedBall center radius, 1 < ‖w‖) ∧
      (∀ w ∈ Metric.closedBall center radius,
        a < (c * w).re ∧ ‖c * w‖ < Q) ∧
      1 + Real.log Q + 5 * eta < a ∧
      Q - lambda + Real.log R + 5 * eta < a := by
  let x : ℝ := ‖c‖
  have hx0 : 0 < x := hc0
  have hx1 : x < 1 := hc1
  let M : ℝ := min (Real.exp lambda) x⁻¹
  have hM1 : 1 < M := by
    exact lt_min (Real.one_lt_exp_iff.mpr hlambda) ((one_lt_inv₀ hx0).mpr hx1)
  let rho : ℝ := (1 + M) / 2
  have hrho1 : 1 < rho := by
    dsimp [rho]
    linarith
  have hrho_exp : rho < Real.exp lambda := by
    have hMexp : M ≤ Real.exp lambda := min_le_left _ _
    dsimp [rho]
    linarith
  have hrho_inv : rho < x⁻¹ := by
    have hMinv : M ≤ x⁻¹ := min_le_right _ _
    dsimp [rho]
    linarith
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho1
  have hxr0 : 0 < x * rho := mul_pos hx0 hrho0
  have hxr1 : x * rho < 1 := by
    rw [inv_eq_one_div] at hrho_inv
    have := (lt_div_iff₀ hx0).mp hrho_inv
    nlinarith
  have hgap1 : 1 + Real.log (x * rho) < x * rho := by
    have hlog := Real.log_lt_sub_one_of_pos hxr0 (ne_of_lt hxr1)
    linarith
  have hlogrho : Real.log rho < lambda :=
    (Real.log_lt_iff_lt_exp hrho0).mpr hrho_exp
  have hgap2 : x * rho - lambda + Real.log rho < x * rho := by
    linarith

  let A : ℝ → ℝ := fun d ↦ x * rho - (x + 1) * d
  let Qd : ℝ → ℝ := fun d ↦ x * rho + (x + 1) * d
  let Rd : ℝ → ℝ := fun d ↦ rho + d
  have hAcont : ContinuousAt A 0 := by fun_prop
  have hQcont : ContinuousAt Qd 0 := by fun_prop
  have hRcont : ContinuousAt Rd 0 := by fun_prop
  have hA0 : A 0 = x * rho := by simp [A]
  have hQ0 : Qd 0 = x * rho := by simp [Qd]
  have hR0 : Rd 0 = rho := by simp [Rd]
  have hApos : ∀ᶠ d : ℝ in 𝓝 0, 0 < A d :=
    continuousAt_const.eventually_lt hAcont (by simpa [hA0] using hxr0)
  have hQpos : ∀ᶠ d : ℝ in 𝓝 0, 0 < Qd d :=
    continuousAt_const.eventually_lt hQcont (by simpa [hQ0] using hxr0)
  have hRpos : ∀ᶠ d : ℝ in 𝓝 0, 0 < Rd d :=
    continuousAt_const.eventually_lt hRcont (by simpa [hR0] using hrho0)
  have hRexp : ∀ᶠ d : ℝ in 𝓝 0, Rd d < Real.exp lambda :=
    hRcont.eventually_lt continuousAt_const (by simpa [hR0] using hrho_exp)
  have hQone : ∀ᶠ d : ℝ in 𝓝 0, Qd d < 1 :=
    hQcont.eventually_lt continuousAt_const (by simpa [hQ0] using hxr1)
  have hext : ∀ᶠ d : ℝ in 𝓝 0, 1 < rho - d := by
    apply (continuousAt_const.eventually_lt (by fun_prop))
    simpa using hrho1
  have hgap1ev : ∀ᶠ d : ℝ in 𝓝 0,
      1 + Real.log (Qd d) + 5 * d < A d := by
    have hleft : ContinuousAt (fun d ↦ 1 + Real.log (Qd d) + 5 * d) 0 := by
      fun_prop (disch := aesop)
    apply hleft.eventually_lt hAcont
    simpa [hA0, hQ0] using hgap1
  have hgap2ev : ∀ᶠ d : ℝ in 𝓝 0,
      Qd d - lambda + Real.log (Rd d) + 5 * d < A d := by
    have hleft : ContinuousAt
        (fun d ↦ Qd d - lambda + Real.log (Rd d) + 5 * d) 0 := by
      fun_prop (disch := aesop)
    apply hleft.eventually_lt hAcont
    simpa [hA0, hQ0, hR0] using hgap2
  have hall : ∀ᶠ d : ℝ in 𝓝 0,
      0 < A d ∧ 0 < Qd d ∧ 0 < Rd d ∧ Rd d < Real.exp lambda ∧
      Qd d < 1 ∧ 1 < rho - d ∧
      1 + Real.log (Qd d) + 5 * d < A d ∧
      Qd d - lambda + Real.log (Rd d) + 5 * d < A d := by
    filter_upwards [hApos, hQpos, hRpos, hRexp, hQone, hext, hgap1ev, hgap2ev]
      with d ha hq hr hre hqo he hg1 hg2
    exact ⟨ha, hq, hr, hre, hqo, he, hg1, hg2⟩
  obtain ⟨d, hd, ha, hq, hr, hre, hqo, he, hg1, hg2⟩ :=
    exists_pos_of_eventually_nhds hall

  let center : ℂ := (rho / x : ℝ) • (starRingEnd ℂ) c
  have hcenter_norm : ‖center‖ = rho := by
    dsimp [center]
    rw [norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs,
      abs_of_pos (div_pos hrho0 hx0)]
    field_simp
    simp [x]
  have hc_center : c * center = (rho * x : ℝ) := by
    dsimp [center]
    rw [mul_comm c, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul]
    push_cast
    simp only [x]
    field_simp
  refine ⟨center, d, A d, Qd d, Rd d, d, hd, ha, hq, hr, hd, ?_, hre, hqo, ?_, ?_, hg1, hg2⟩
  · rw [hcenter_norm]
  · intro w hw
    have hw' : ‖w - center‖ ≤ d := by
      simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
    have hwlower : rho - d ≤ ‖w‖ := by
      have hh : ‖center‖ - ‖w‖ ≤ d := by
        exact (norm_sub_norm_le center w).trans (by simpa [norm_sub_rev] using hw')
      rw [hcenter_norm] at hh
      linarith
    exact he.trans_le hwlower
  · intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hdiff : ‖c * w - c * center‖ ≤ x * d := by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left hw hx0.le
    have hdiff' : ‖c * w - (rho * x : ℝ)‖ ≤ x * d := by
      simpa [hc_center] using hdiff
    constructor
    · have hre_lower : (c * center).re - ‖c * w - c * center‖ ≤ (c * w).re := by
        have := neg_le_of_abs_le (Complex.abs_re_le_norm (c * w - c * center))
        rw [Complex.sub_re] at this
        linarith
      rw [hc_center, Complex.ofReal_re] at hre_lower
      dsimp [A]
      nlinarith [hdiff']
    · have hnorm : ‖c * w‖ ≤ ‖c * center‖ + ‖c * w - c * center‖ := by
        calc
          ‖c * w‖ = ‖c * center + (c * w - c * center)‖ := by congr 1 <;> ring
          _ ≤ _ := norm_add_le _ _
      rw [hc_center, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hrho0 hx0)] at hnorm
      dsimp [Qd]
      nlinarith [hdiff']

end Erdos973
