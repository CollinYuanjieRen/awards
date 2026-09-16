import MerLeanExperiment.GridScalarDefinitions
import MerLeanExperiment.GridRatio
import Mathlib.Tactic

namespace Erdos441

/-- For every sufficiently fine source grid, the fourth-case scalar residual is
nonnegative uniformly for all admissible values of `u`. -/
theorem grid_case4_scalar : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ u : ℝ,
    2 ≤ u → 0 ≤ u * gridSlope4 (gridQ L) + 2 - 3 * Real.sqrt 2 / 2 +
      gridEta * Real.sqrt 2 - gridQ L / (4 * u) := by
  let D : ℝ → ℝ := fun q ↦ gridSlope4 q
  let E : ℝ → ℝ := fun q ↦ gridResidual4 q
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : 12 * Real.sqrt 2 < 17 := by
    nlinarith [sq_nonneg (12 * Real.sqrt 2 + 17)]
  have hDone : 0 < D 1 := by
    dsimp [D, gridSlope4, gridEta]
    nlinarith
  have hEone : 0 < E 1 := by
    dsimp [E, gridResidual4, gridSlope4, gridEta]
    nlinarith
  have hDcont : ContinuousAt D 1 := by
    dsimp [D, gridSlope4]
    fun_prop (disch := norm_num)
  have hEcont : ContinuousAt E 1 := by
    dsimp [E, gridResidual4, gridSlope4]
    fun_prop (disch := norm_num)
  have hDevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < D (gridQ L) :=
    (hDcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hDone)
  have hEevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < E (gridQ L) :=
    (hEcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hEone)
  obtain ⟨Lbase, hLbase⟩ := Filter.eventually_atTop.1 (hDevent.and hEevent)
  refine ⟨max 1 Lbase, le_max_left _ _, ?_⟩
  intro L hL u hu
  have hLone : 1 ≤ L := le_trans (le_max_left 1 Lbase) hL
  have hLbase' : Lbase ≤ L := le_trans (le_max_right 1 Lbase) hL
  have hDE := hLbase L hLbase'
  have hqpos : 0 < gridQ L := (grid_ratio_spec L hLone).1.trans' zero_lt_one
  have huPos : 0 < u := by linarith
  have hDu : 2 * D (gridQ L) ≤ u * D (gridQ L) := by
    exact mul_le_mul_of_nonneg_right hu hDE.1.le
  have hfrac : gridQ L / (4 * u) ≤ gridQ L / 8 := by
    apply (div_le_div_iff_of_pos_left hqpos (by positivity) (by norm_num)).2
    nlinarith
  have hE : 0 ≤ E (gridQ L) := hDE.2.le
  dsimp [E, gridResidual4] at hE
  dsimp [D] at hDu
  nlinarith

end Erdos441

