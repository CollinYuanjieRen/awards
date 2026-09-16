import MerLeanExperiment.FiniteParameters
import MerLeanExperiment.PhaseStability
import MerLeanExperiment.ExponentialExceptionalSafety

open Set MeasureTheory
open scoped ENNReal

namespace Erdos492Real

noncomputable section

/-- The concrete exponential subdivisions satisfy Schmidt's finite quantitative
subdivision lemma. -/
theorem finite_subdivision_lemma : FiniteSubdivisionLemma := by
  intro N ε hε
  let δ : ℝ := min (1 / 4) (ε / 64)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδsmall : 16 * δ ≤ ε / 4 := by
    have := min_le_right (1 / 4 : ℝ) (ε / 64)
    dsimp [δ]
    nlinarith
  obtain ⟨q, hq, hbottom, hmesh, happ⟩ :=
    exists_finite_parameters N hε hδ0
  have hbottom' : exponentialGridPoint q 0 < ε := by
    simpa [exponentialGridPoint] using hbottom.trans (by linarith : ε / 4 < ε)
  refine ⟨exponentialDivision q hq,
    exponentialDivision_fine q hq ε hbottom' hmesh, ?_⟩
  refine ⟨exponentialExceptionalSet q δ,
    measurableSet_exponentialExceptionalSet q δ, ?_, ?_⟩
  · refine (volume_exponentialExceptionalSet_le q hq hδ0 hδ1).trans_lt ?_
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by nlinarith)
  · intro x hx0 hx1 hxE m hm1 hmN hmx1
    obtain ⟨hxbot, hleft, hright, hthreshold⟩ :=
      exponentialExceptionalSet_safe q hq hδ0 hδ1 hx0 hx1 hxE
    have hxpos : 0 < x := (Real.exp_pos _).trans hxbot
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m by omega)
    have hmxpos : 0 < (m : ℝ) * x := mul_pos hmpos hxpos
    obtain ⟨z, hz⟩ := happ m hmN
    have hphase :
        (Int.fract ((q : ℝ) * Real.log ((m : ℝ) * x)) < phaseThreshold q ↔
          Int.fract ((q : ℝ) * Real.log x) < phaseThreshold q) :=
      fract_threshold_stable z
        (logarithmic_phase_error q z hmpos hxpos hz) hleft hright hthreshold
    have hxbridge := divisionSign_exponentialPoints_eq_phaseSign q hq hxbot.le hx1
    have hmxbot : exponentialGridPoint q 0 ≤ (m : ℝ) * x := by
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hxle : x ≤ (m : ℝ) * x := by nlinarith
      exact hxbot.le.trans hxle
    have hmxbridge :=
      divisionSign_exponentialPoints_eq_phaseSign q hq hmxbot hmx1
    change divisionSign (exponentialPoints q : Set ℝ) ((m : ℝ) * x) =
      divisionSign (exponentialPoints q : Set ℝ) x
    rw [hmxbridge, hxbridge]
    unfold phaseSign
    by_cases hp : Int.fract ((q : ℝ) * Real.log ((m : ℝ) * x)) < phaseThreshold q
    · have hxphase := hphase.mp hp
      simp [hp, hxphase]
    · have hxphase : ¬Int.fract ((q : ℝ) * Real.log x) < phaseThreshold q := by
        exact fun h => hp (hphase.mpr h)
      simp [hp, hxphase]

end

end Erdos492Real
