import MerLeanExperiment.TriangleCyclePattern
import MerLeanExperiment.ColoringClauses
import MerLeanExperiment.Certificates.Z8DirectTriangleCycle5.Complete
namespace CochromaticTwenty.TriangleCycleMeaning
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
open CochromaticTwenty.Certificates.Z8DirectTriangleCycle5
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def covers : Fin 83 → ColoringClauseWitness 8 3 :=
  ![
    ⟨![{0, 3}, {1, 4, 5}, {2, 6, 7}], ![false, true, true]⟩,
    ⟨![{0, 3}, {1, 4, 6}, {2, 5, 7}], ![false, false, false]⟩,
    ⟨![{0, 3}, {1, 4, 7}, {2, 5, 6}], ![false, false, true]⟩,
    ⟨![{0, 3}, {1, 5, 6}, {2, 4, 7}], ![false, true, false]⟩,
    ⟨![{0, 3}, {1, 5, 7}, {2, 4, 6}], ![false, false, false]⟩,
    ⟨![{0, 3}, {1, 6, 7}, {2, 4, 5}], ![false, true, true]⟩,
    ⟨![{0, 3}, {1, 2, 4, 5}, {6, 7}], ![false, true, false]⟩,
    ⟨![{0, 3}, {1, 2, 6, 7}, {4, 5}], ![false, true, false]⟩,
    ⟨![{0, 4}, {1, 3, 5}, {2, 6, 7}], ![false, false, true]⟩,
    ⟨![{0, 4}, {1, 3, 6}, {2, 5, 7}], ![false, false, false]⟩,
    ⟨![{0, 4}, {1, 3, 7}, {2, 5, 6}], ![false, true, true]⟩,
    ⟨![{0, 4}, {1, 5, 7}, {2, 3, 6}], ![false, false, false]⟩,
    ⟨![{0, 4}, {1, 6, 7}, {2, 3, 5}], ![false, true, false]⟩,
    ⟨![{0, 4}, {1, 2, 3, 7}, {5, 6}], ![false, true, false]⟩,
    ⟨![{0, 5}, {1, 3, 4}, {2, 6, 7}], ![false, true, true]⟩,
    ⟨![{0, 5}, {1, 3, 6}, {2, 4, 7}], ![false, false, false]⟩,
    ⟨![{0, 5}, {1, 4, 6}, {2, 3, 7}], ![false, false, true]⟩,
    ⟨![{0, 5}, {1, 4, 7}, {2, 3, 6}], ![false, false, false]⟩,
    ⟨![{0, 5}, {1, 6, 7}, {2, 3, 4}], ![false, true, true]⟩,
    ⟨![{0, 5}, {1, 2, 3, 4}, {6, 7}], ![false, true, false]⟩,
    ⟨![{0, 6}, {1, 3, 4}, {2, 5, 7}], ![false, true, false]⟩,
    ⟨![{0, 6}, {1, 3, 5}, {2, 4, 7}], ![false, false, false]⟩,
    ⟨![{0, 6}, {1, 4, 5}, {2, 3, 7}], ![false, true, true]⟩,
    ⟨![{0, 6}, {1, 4, 7}, {2, 3, 5}], ![false, false, false]⟩,
    ⟨![{0, 6}, {1, 5, 7}, {2, 3, 4}], ![false, false, true]⟩,
    ⟨![{0, 7}, {1, 3, 4}, {2, 5, 6}], ![false, true, true]⟩,
    ⟨![{0, 7}, {1, 3, 6}, {2, 4, 5}], ![false, false, true]⟩,
    ⟨![{0, 7}, {1, 4, 5}, {2, 3, 6}], ![false, true, false]⟩,
    ⟨![{0, 7}, {1, 4, 6}, {2, 3, 5}], ![false, false, false]⟩,
    ⟨![{0, 1, 3}, {2, 4, 5}, {6, 7}], ![true, true, false]⟩,
    ⟨![{0, 1, 3}, {2, 4, 7}, {5, 6}], ![true, false, false]⟩,
    ⟨![{0, 1, 3}, {2, 5, 7}, {4, 6}], ![true, false, false]⟩,
    ⟨![{0, 1, 4}, {2, 3, 6}, {5, 7}], ![true, false, false]⟩,
    ⟨![{0, 1, 4}, {2, 3, 7}, {5, 6}], ![true, true, false]⟩,
    ⟨![{0, 1, 4}, {2, 5, 6}, {3, 7}], ![true, true, false]⟩,
    ⟨![{0, 1, 4}, {2, 5, 7}, {3, 6}], ![true, false, false]⟩,
    ⟨![{0, 1, 5}, {2, 3, 4}, {6, 7}], ![true, true, false]⟩,
    ⟨![{0, 1, 6}, {2, 3, 7}, {4, 5}], ![true, true, false]⟩,
    ⟨![{0, 1, 6}, {2, 4, 5}, {3, 7}], ![true, true, false]⟩,
    ⟨![{0, 1, 6}, {2, 5, 7}, {3, 4}], ![true, false, false]⟩,
    ⟨![{0, 1, 7}, {2, 3, 6}, {4, 5}], ![true, false, false]⟩,
    ⟨![{0, 1, 7}, {2, 5, 6}, {3, 4}], ![true, true, false]⟩,
    ⟨![{0, 2, 3}, {1, 4, 7}, {5, 6}], ![true, false, false]⟩,
    ⟨![{0, 2, 3}, {1, 6, 7}, {4, 5}], ![true, true, false]⟩,
    ⟨![{0, 2, 4}, {1, 3, 7}, {5, 6}], ![true, true, false]⟩,
    ⟨![{0, 2, 5}, {1, 4, 6}, {3, 7}], ![true, false, false]⟩,
    ⟨![{0, 3, 4}, {1, 5}, {2, 6, 7}], ![true, false, true]⟩,
    ⟨![{0, 3, 4}, {1, 6}, {2, 5, 7}], ![true, false, false]⟩,
    ⟨![{0, 3, 4}, {1, 7}, {2, 5, 6}], ![true, false, true]⟩,
    ⟨![{0, 3, 4}, {1, 6, 7}, {2, 5}], ![true, true, false]⟩,
    ⟨![{0, 3, 5}, {1, 6}, {2, 4, 7}], ![false, false, false]⟩,
    ⟨![{0, 3, 5}, {1, 2, 4}, {6, 7}], ![false, true, false]⟩,
    ⟨![{0, 3, 5}, {1, 4, 7}, {2, 6}], ![false, false, false]⟩,
    ⟨![{0, 3, 5}, {1, 6, 7}, {2, 4}], ![false, true, false]⟩,
    ⟨![{0, 3, 6}, {1, 4}, {2, 5, 7}], ![false, false, false]⟩,
    ⟨![{0, 3, 6}, {1, 5}, {2, 4, 7}], ![false, false, false]⟩,
    ⟨![{0, 3, 6}, {1, 7}, {2, 4, 5}], ![false, false, true]⟩,
    ⟨![{0, 3, 6}, {1, 2, 7}, {4, 5}], ![false, true, false]⟩,
    ⟨![{0, 3, 6}, {1, 4, 7}, {2, 5}], ![false, false, false]⟩,
    ⟨![{0, 3, 7}, {1, 6}, {2, 4, 5}], ![true, false, true]⟩,
    ⟨![{0, 3, 7}, {1, 2, 6}, {4, 5}], ![true, true, false]⟩,
    ⟨![{0, 4, 5}, {1, 7}, {2, 3, 6}], ![true, false, false]⟩,
    ⟨![{0, 4, 5}, {1, 2, 7}, {3, 6}], ![true, true, false]⟩,
    ⟨![{0, 4, 5}, {1, 3, 6}, {2, 7}], ![true, false, false]⟩,
    ⟨![{0, 4, 5}, {1, 3, 7}, {2, 6}], ![true, true, false]⟩,
    ⟨![{0, 4, 5}, {1, 6, 7}, {2, 3}], ![true, true, false]⟩,
    ⟨![{0, 4, 6}, {1, 3}, {2, 5, 7}], ![false, false, false]⟩,
    ⟨![{0, 4, 6}, {1, 5}, {2, 3, 7}], ![false, false, true]⟩,
    ⟨![{0, 4, 6}, {1, 2, 3}, {5, 7}], ![false, true, false]⟩,
    ⟨![{0, 4, 7}, {1, 3}, {2, 5, 6}], ![false, false, true]⟩,
    ⟨![{0, 4, 7}, {1, 5}, {2, 3, 6}], ![false, false, false]⟩,
    ⟨![{0, 4, 7}, {1, 2, 3}, {5, 6}], ![false, true, false]⟩,
    ⟨![{0, 4, 7}, {1, 2, 6}, {3, 5}], ![false, true, false]⟩,
    ⟨![{0, 4, 7}, {1, 3, 5}, {2, 6}], ![false, false, false]⟩,
    ⟨![{0, 5, 6}, {1, 3}, {2, 4, 7}], ![true, false, false]⟩,
    ⟨![{0, 5, 6}, {1, 2, 7}, {3, 4}], ![true, true, false]⟩,
    ⟨![{0, 5, 7}, {1, 4}, {2, 3, 6}], ![false, false, false]⟩,
    ⟨![{0, 5, 7}, {1, 3, 6}, {2, 4}], ![false, false, false]⟩,
    ⟨![{0, 6, 7}, {1, 5}, {2, 3, 4}], ![true, false, true]⟩,
    ⟨![{0, 1, 2, 3}, {4, 5}, {6, 7}], ![true, false, false]⟩,
    ⟨![{0, 1, 2, 4}, {3, 5}, {6, 7}], ![true, false, false]⟩,
    ⟨![{0, 1, 2, 6}, {3, 4}, {5, 7}], ![true, false, false]⟩,
    ⟨![{0, 1, 2, 7}, {3, 4}, {5, 6}], ![true, false, false]⟩]
theorem covers_valid : ∀ i : Fin 83,
    (covers i).Valid triangleCyclePattern
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map
        (fun l => (l.1.val - 1, l.2))) := by
  decide +kernel

theorem inputClause_explained (i : ℕ) (hi : i < 83) :
    ∃ w : ColoringClauseWitness 8 3, w.Valid triangleCyclePattern
      ((inputClause (i + 1)).clause.map (fun l => (l.1.val - 1, l.2))) := by
  refine ⟨covers ⟨i, hi⟩, ?_⟩
  have hlt : i < 250 := by omega
  simpa [inputClause, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] using
    covers_valid ⟨i, hi⟩

theorem all_inputs_explained : ∀ c ∈ concreteCNF.clauses,
    ∃ w : ColoringClauseWitness 8 3, w.Valid triangleCyclePattern c := by
  intro c hc
  simp [concreteCNF, indexedCNF] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact inputClause_explained i hi

theorem triangleCycle_hasCocoloring (a : ℕ → Bool) :
    HasCocoloring (triangleCyclePattern.graph a) 3 :=
  cocoloring_of_cover_clauses_unsat triangleCyclePattern concreteCNF
    concreteCNF_unsat all_inputs_explained a
end CochromaticTwenty.TriangleCycleMeaning
#print axioms CochromaticTwenty.TriangleCycleMeaning.triangleCycle_hasCocoloring
