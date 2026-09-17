import MerLeanExperiment.B16Meaning.B16_3_2.Block00
import MerLeanExperiment.B16Meaning.B16_3_2.Block01
import MerLeanExperiment.Certificates.B16_3_2.Complete
namespace CochromaticTwenty.B16Meaning.B16_3_2
open Std.Sat
open CochromaticTwenty.Certificates.B16_3_2
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
theorem inputClause_explained (i : ℕ) (hi : i < 398) :
    (∃ w : ForbiddenFourClauseWitness 16, w.Valid (neighborhoodPattern 16 7 483585 60117131)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2)))) ∨
    (∃ code ∈ allowedCodes, ClauseForcesCode (neighborhoodPattern 16 7 483585 60117131)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2))) code) := by
  have hmod := Nat.mod_lt i (by decide : 0 < 250)
  have hdiv := Nat.mod_add_div i 250
  have hquot : i / 250 < 2 := by omega
  interval_cases hq : i / 250
  · have hr : i % 250 < 250 := by omega
    have hv := witnesses0_valid ⟨i % 250, hr⟩
    cases he : witnesses0 ⟨i % 250, hr⟩ with
    | inl w =>
      left; refine ⟨w, ?_⟩
      simpa [ClassificationClauseValid, he, inputClause, hq] using hv
    | inr code =>
      right; refine ⟨code, ?_⟩
      simpa [ClassificationClauseValid, he, inputClause, hq] using hv
  · have hr : i % 250 < 148 := by omega
    have hv := witnesses1_valid ⟨i % 250, hr⟩
    cases he : witnesses1 ⟨i % 250, hr⟩ with
    | inl w =>
      left; refine ⟨w, ?_⟩
      simpa [ClassificationClauseValid, he, inputClause, hq] using hv
    | inr code =>
      right; refine ⟨code, ?_⟩
      simpa [ClassificationClauseValid, he, inputClause, hq] using hv
theorem all_inputs_explained : ∀ c ∈ concreteCNF.clauses,
    (∃ w : ForbiddenFourClauseWitness 16, w.Valid (neighborhoodPattern 16 7 483585 60117131) c) ∨
    (∃ code ∈ allowedCodes, ClauseForcesCode (neighborhoodPattern 16 7 483585 60117131) c code) := by
  intro c hc
  simp only [concreteCNF, indexedCNF, List.mem_toArray, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact inputClause_explained i hi
theorem classification (a : ℕ → Bool) (hno : NoHomogeneousFour ((neighborhoodPattern 16 7 483585 60117131).graph a)) :
    Nonempty ((neighborhoodPattern 16 7 483585 60117131).graph a ≃g codeGraph 16 coreCode0) ∨
    Nonempty ((neighborhoodPattern 16 7 483585 60117131).graph a ≃g codeGraph 16 coreCode1) := by
  obtain ⟨c, hc, heq⟩ := classification_of_clauses_unsat (neighborhoodPattern 16 7 483585 60117131) concreteCNF
    allowedCodes concreteCNF_unsat all_inputs_explained a hno
  rw [heq]
  exact allowedCodes_iso c hc
end CochromaticTwenty.B16Meaning.B16_3_2
#print axioms CochromaticTwenty.B16Meaning.B16_3_2.classification
