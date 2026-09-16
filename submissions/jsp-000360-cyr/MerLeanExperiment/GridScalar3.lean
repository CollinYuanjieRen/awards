import MerLeanExperiment.GridScalarDefinitions
import MerLeanExperiment.GridRatio
import MerLeanExperiment.QuadraticChord
import Mathlib.Tactic

namespace Erdos441

/-- For all sufficiently fine source grids, the exact third-case residual is
nonnegative throughout its full real endpoint interval. -/
theorem grid_case3_scalar : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ u : ℝ,
    Real.sqrt 2 ≤ u → u ≤ 2 / gridQ L → 0 ≤ gridResidual3 (gridQ L) u := by
  let F : ℝ → ℝ := fun q ↦ 1 / q - Real.sqrt 2 * (1 / 2 + gridEta)
  let G : ℝ → ℝ := fun q ↦
    9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta - 2 * gridEta -
      3 / (2 * q) - 3 * q / 2
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : 13 * Real.sqrt 2 < 23 := by
    nlinarith [sq_nonneg (13 * Real.sqrt 2 + 23)]
  have hlarge : 65 < 48 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (48 * Real.sqrt 2 + 65)]
  have hFone : 0 < F 1 := by
    dsimp [F, gridEta]
    nlinarith
  have hGone : 0 < G 1 := by
    dsimp [G, gridEta]
    nlinarith
  have hFcont : ContinuousAt F 1 := by
    dsimp [F]
    fun_prop (disch := norm_num)
  have hGcont : ContinuousAt G 1 := by
    dsimp [G]
    fun_prop (disch := norm_num)
  have hFevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < F (gridQ L) :=
    (hFcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hFone)
  have hGevent : ∀ᶠ L : ℕ in Filter.atTop, 0 < G (gridQ L) :=
    (hGcont.tendsto.comp gridQ_tendsto_one).eventually (lt_mem_nhds hGone)
  obtain ⟨Lbase, hLbase⟩ := Filter.eventually_atTop.1 (hFevent.and hGevent)
  refine ⟨max 1 Lbase, le_max_left _ _, ?_⟩
  intro L hL u huLower huUpper
  have hLone : 1 ≤ L := le_trans (le_max_left 1 Lbase) hL
  have hLbase' : Lbase ≤ L := le_trans (le_max_right 1 Lbase) hL
  have hFG := hLbase L hLbase'
  have hspec := grid_ratio_spec L hLone
  have hq : 1 < gridQ L := hspec.1
  have hqpos : 0 < gridQ L := zero_lt_one.trans hq
  have heta : 0 < gridEta := hspec.2.2.2
  let q : ℝ := gridQ L
  have hq' : 1 < q := hq
  have hqpos' : 0 < q := hqpos
  have hFq : 0 < F q := hFG.1
  have hGq : 0 < G q := hFG.2
  have hleftEq : gridResidual3 q (Real.sqrt 2) = (q - 1) * F q := by
    dsimp [gridResidual3, F]
    field_simp [hqpos'.ne', hspos.ne']
    nlinarith
  have hrightEq : gridResidual3 q (2 / q) = G q := by
    dsimp [gridResidual3, G]
    field_simp [hqpos'.ne']
    ring
  have hleft : 0 ≤ gridResidual3 q (Real.sqrt 2) := by
    rw [hleftEq]
    exact mul_nonneg (sub_nonneg.mpr hq'.le) hFq.le
  have hright : 0 ≤ gridResidual3 q (2 / q) := by
    rw [hrightEq]
    exact hGq.le
  let A : ℝ := -q / 2 - 1 / 4 - gridEta * q
  let B : ℝ := 9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta + 1 - 1 / q
  have hA : A ≤ 0 := by
    dsimp [A]
    have : 0 ≤ gridEta * q := mul_nonneg heta.le hqpos'.le
    nlinarith
  have hmulEq (v : ℝ) (hv : v ≠ 0) :
      v * gridResidual3 q v = A * v ^ 2 + B * v - 3 := by
    dsimp [gridResidual3, A, B]
    field_simp [hqpos'.ne', hv]
    ring
  have hquadLeft : 0 ≤ A * (Real.sqrt 2) ^ 2 + B * Real.sqrt 2 - 3 := by
    rw [← hmulEq (Real.sqrt 2) hspos.ne']
    exact mul_nonneg hs0 hleft
  have hbpos : 0 < 2 / q := div_pos (by norm_num) hqpos'
  have hquadRight : 0 ≤ A * (2 / q) ^ 2 + B * (2 / q) - 3 := by
    rw [← hmulEq (2 / q) hbpos.ne']
    exact mul_nonneg hbpos.le hright
  have huLower' : Real.sqrt 2 ≤ u := huLower
  have huUpper' : u ≤ 2 / q := huUpper
  have hquad := quadratic_nonneg_between (Real.sqrt 2) (2 / q) u A B (-3)
    huLower' huUpper' hA (by simpa using hquadLeft) (by simpa using hquadRight)
  have hupos : 0 < u := hspos.trans_le huLower
  have hquad' : 0 ≤ A * u ^ 2 + B * u - 3 := by
    simpa only [sub_eq_add_neg] using hquad
  rw [← hmulEq u hupos.ne'] at hquad'
  change 0 ≤ gridResidual3 q u
  exact nonneg_of_mul_nonneg_right hquad' hupos

end Erdos441
