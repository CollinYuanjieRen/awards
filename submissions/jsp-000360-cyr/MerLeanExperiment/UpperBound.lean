import MerLeanExperiment.ConcreteUpper
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos441

theorem chen_uniform_upper : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, LcmBounded N A →
      (A.card : ℝ) ≤ (Real.sqrt (9 / 8 : ℝ) + ε) * Real.sqrt N := by
  intro epsilon hepsilon
  obtain ⟨L0, hL0, hconcrete⟩ := eventually_concrete_upper
  have hgap : Filter.Tendsto (fun L : ℕ => 1 - gridQ L ^ (-1 : ℤ))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hh := (gridQ_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_sub 1
    simpa only [inv_one, sub_self, zpow_neg_one] using hh
  have hpower : Filter.Tendsto (fun S : ℕ => (1 / 2 : ℝ) ^ S)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (hgap.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < epsilon / 3)))
  obtain ⟨NS, hNS⟩ := Filter.eventually_atTop.mp
    (hpower.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < epsilon / 3)))
  let L := max L0 NL
  let S := max 1 NS
  let c : ℝ := Real.sqrt (9 / 8 : ℝ)
  have hc : 0 < c + 1 := by dsimp [c]; positivity
  let rho : ℝ := epsilon / (3 * (c + 1))
  have hrho : 0 < rho := div_pos hepsilon (by positivity)
  have hrhoc : rho * (c + 1) = epsilon / 3 := by
    dsimp [rho]
    field_simp
  obtain ⟨N0, _, hN0⟩ := hconcrete L (le_max_left _ _) S (le_max_left _ _) rho hrho
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hbound := hN0 N hN A hA
  have hgl := hNL L (le_max_right _ _)
  have hps := hNS S (le_max_right _ _)
  have hcoef : c + (1 - gridQ L ^ (-1 : ℤ)) + (1 / 2 : ℝ) ^ S + rho * (c + 1) ≤
      c + epsilon := by
    rw [hrhoc]
    change 1 - gridQ L ^ (-1 : ℤ) < epsilon / 3 at hgl
    change (1 / 2 : ℝ) ^ S < epsilon / 3 at hps
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _))

end Erdos441

#print axioms Erdos441.chen_uniform_upper
