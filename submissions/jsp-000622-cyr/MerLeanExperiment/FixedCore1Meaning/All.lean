import MerLeanExperiment.FixedCore1Meaning.Block00
import MerLeanExperiment.FixedCore1Meaning.Block01
import MerLeanExperiment.FixedCore1Meaning.Block02
import MerLeanExperiment.FixedCore1Meaning.Block03
import MerLeanExperiment.FixedCore1Meaning.Block04
import MerLeanExperiment.FixedCore1Meaning.Block05
import MerLeanExperiment.FixedCore1Meaning.Block06
import MerLeanExperiment.FixedCore1Meaning.Block07
import MerLeanExperiment.FixedCore1Meaning.Block08
import MerLeanExperiment.FixedCore1Meaning.Block09
import MerLeanExperiment.FixedCore1Meaning.Block10
import MerLeanExperiment.FixedCore1Meaning.Block11
import MerLeanExperiment.FixedCore1Meaning.Block12
import MerLeanExperiment.FixedCore1Meaning.Block13
import MerLeanExperiment.FixedCore1Meaning.Block14
import MerLeanExperiment.FixedCore1Meaning.Block15
import MerLeanExperiment.FixedCore1Meaning.Block16
import MerLeanExperiment.FixedCore1Meaning.Block17
import MerLeanExperiment.FixedCore1Meaning.Block18
import MerLeanExperiment.FixedCore1Meaning.Block19
import MerLeanExperiment.FixedCore1Meaning.Block20
import MerLeanExperiment.FixedCore1Meaning.Block21
import MerLeanExperiment.FixedCore1Meaning.Block22
import MerLeanExperiment.FixedCore1Meaning.Block23
import MerLeanExperiment.Certificates.FixedCore1.Inputs
namespace CochromaticTwenty.FixedCore1Meaning
open Std.Sat
open CochromaticTwenty.Certificates.FixedCore1
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
theorem inputClause_explained (i : ℕ) (hi : i < 5880) :
    ∃ w : PairClauseWitness 20, w.Valid (fixedCorePattern coreCode1)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2))) := by
  have hmod := Nat.mod_lt i (by decide : 0 < 250)
  have hdiv := Nat.mod_add_div i 250
  have hquot : i / 250 < 24 := by omega
  interval_cases hq : i / 250
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock0 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock0_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock1 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock1_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock2 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock2_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock3 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock3_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock4 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock4_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock5 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock5_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock6 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock6_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock7 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock7_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock8 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock8_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock9 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock9_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock10 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock10_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock11 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock11_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock12 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock12_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock13 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock13_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock14 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock14_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock15 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock15_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock16 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock16_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock17 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock17_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock18 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock18_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock19 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock19_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock20 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock20_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock21 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock21_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock22 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock22_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 130 := by omega
    refine ⟨pairBlock23 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock23_valid ⟨i % 250, hr⟩
theorem all_inputs_explained : ∀ c ∈ concreteCNF.clauses,
    ∃ w : PairClauseWitness 20, w.Valid (fixedCorePattern coreCode1) c := by
  intro c hc
  simp [concreteCNF, indexedCNF] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact inputClause_explained i hi
end CochromaticTwenty.FixedCore1Meaning
#print axioms CochromaticTwenty.FixedCore1Meaning.all_inputs_explained
