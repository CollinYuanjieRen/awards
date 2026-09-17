import MerLeanExperiment.FixedCore0Meaning.Block00
import MerLeanExperiment.FixedCore0Meaning.Block01
import MerLeanExperiment.FixedCore0Meaning.Block02
import MerLeanExperiment.FixedCore0Meaning.Block03
import MerLeanExperiment.FixedCore0Meaning.Block04
import MerLeanExperiment.FixedCore0Meaning.Block05
import MerLeanExperiment.FixedCore0Meaning.Block06
import MerLeanExperiment.FixedCore0Meaning.Block07
import MerLeanExperiment.FixedCore0Meaning.Block08
import MerLeanExperiment.FixedCore0Meaning.Block09
import MerLeanExperiment.FixedCore0Meaning.Block10
import MerLeanExperiment.FixedCore0Meaning.Block11
import MerLeanExperiment.FixedCore0Meaning.Block12
import MerLeanExperiment.FixedCore0Meaning.Block13
import MerLeanExperiment.FixedCore0Meaning.Block14
import MerLeanExperiment.FixedCore0Meaning.Block15
import MerLeanExperiment.FixedCore0Meaning.Block16
import MerLeanExperiment.FixedCore0Meaning.Block17
import MerLeanExperiment.FixedCore0Meaning.Block18
import MerLeanExperiment.FixedCore0Meaning.Block19
import MerLeanExperiment.FixedCore0Meaning.Block20
import MerLeanExperiment.FixedCore0Meaning.Block21
import MerLeanExperiment.FixedCore0Meaning.Block22
import MerLeanExperiment.FixedCore0Meaning.Block23
import MerLeanExperiment.FixedCore0Meaning.Block24
import MerLeanExperiment.FixedCore0Meaning.Block25
import MerLeanExperiment.FixedCore0Meaning.Block26
import MerLeanExperiment.FixedCore0Meaning.Block27
import MerLeanExperiment.FixedCore0Meaning.Block28
import MerLeanExperiment.FixedCore0Meaning.Block29
import MerLeanExperiment.FixedCore0Meaning.Block30
import MerLeanExperiment.Certificates.FixedCore0.Inputs
namespace CochromaticTwenty.FixedCore0Meaning
open Std.Sat
open CochromaticTwenty.Certificates.FixedCore0
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
theorem inputClause_explained (i : ℕ) (hi : i < 7550) :
    ∃ w : PairClauseWitness 20, w.Valid (fixedCorePattern coreCode0)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2))) := by
  have hmod := Nat.mod_lt i (by decide : 0 < 250)
  have hdiv := Nat.mod_add_div i 250
  have hquot : i / 250 < 31 := by omega
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
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock23 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock23_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock24 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock24_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock25 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock25_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock26 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock26_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock27 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock27_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock28 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock28_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 250 := by omega
    refine ⟨pairBlock29 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock29_valid ⟨i % 250, hr⟩
  · have hr : i % 250 < 50 := by omega
    refine ⟨pairBlock30 ⟨i % 250, hr⟩, ?_⟩
    simpa [inputClause, hq] using pairBlock30_valid ⟨i % 250, hr⟩
theorem all_inputs_explained : ∀ c ∈ concreteCNF.clauses,
    ∃ w : PairClauseWitness 20, w.Valid (fixedCorePattern coreCode0) c := by
  intro c hc
  simp [concreteCNF, indexedCNF] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact inputClause_explained i hi
end CochromaticTwenty.FixedCore0Meaning
#print axioms CochromaticTwenty.FixedCore0Meaning.all_inputs_explained
