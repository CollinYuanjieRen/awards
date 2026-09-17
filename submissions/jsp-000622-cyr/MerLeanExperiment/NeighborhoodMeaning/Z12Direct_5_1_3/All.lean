import MerLeanExperiment.NeighborhoodMeaning.Z12Direct_5_1_3.Block00
import MerLeanExperiment.Certificates.Z12Direct_5_1_3.Complete
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_1_3
open Std.Sat
open CochromaticTwenty.Certificates.Z12Direct_5_1_3
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
theorem inputClause_explained (i : ℕ) (hi : i < 120) :
    (∃ w : ColoringClauseWitness 12 4, w.Valid (neighborhoodPattern 12 5 736 7952)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2)))) ∨
    (∃ w : ForbiddenFourClauseWitness 12, w.Valid (neighborhoodPattern 12 5 736 7952)
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2)))) := by
  have hmod := Nat.mod_lt i (by decide : 0 < 250)
  have hdiv := Nat.mod_add_div i 250
  have hquot : i / 250 < 1 := by omega
  interval_cases hq : i / 250
  · have hr : i % 250 < 120 := by omega
    have hv := witnesses0_valid ⟨i % 250, hr⟩
    cases he : witnesses0 ⟨i % 250, hr⟩ with
    | inl w =>
      left; refine ⟨w, ?_⟩
      simpa [ColoringOrForbiddenValid, he, inputClause, hq] using hv
    | inr w =>
      right; refine ⟨w, ?_⟩
      simpa [ColoringOrForbiddenValid, he, inputClause, hq] using hv
theorem all_inputs_explained : ∀ c ∈ concreteCNF.clauses,
    (∃ w : ColoringClauseWitness 12 4, w.Valid (neighborhoodPattern 12 5 736 7952) c) ∨
    (∃ w : ForbiddenFourClauseWitness 12, w.Valid (neighborhoodPattern 12 5 736 7952) c) := by
  intro c hc
  simp only [concreteCNF, indexedCNF, List.mem_toArray, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact inputClause_explained i hi
theorem hasCocoloring (a : ℕ → Bool) (hno : NoHomogeneousFour ((neighborhoodPattern 12 5 736 7952).graph a)) :
    HasCocoloring ((neighborhoodPattern 12 5 736 7952).graph a) 4 :=
  cocoloring_of_unsat (neighborhoodPattern 12 5 736 7952) concreteCNF concreteCNF_unsat all_inputs_explained a hno
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_1_3
#print axioms CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_1_3.hasCocoloring
