import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_3_10.Clauses0000_0026
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_3_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_3_10
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 27 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{4, 5, 6, 7}, false⟩,
    .inr ⟨{4, 5, 8, 9}, false⟩,
    .inr ⟨{4, 5, 10, 11}, false⟩,
    .inr ⟨{4, 6, 8, 10}, true⟩,
    .inr ⟨{4, 6, 8, 11}, true⟩,
    .inr ⟨{4, 6, 9, 10}, true⟩,
    .inr ⟨{4, 6, 9, 11}, true⟩,
    .inr ⟨{4, 7, 8, 10}, true⟩,
    .inr ⟨{4, 7, 8, 11}, true⟩,
    .inr ⟨{4, 7, 9, 10}, true⟩,
    .inr ⟨{4, 7, 9, 11}, true⟩,
    .inr ⟨{5, 6, 8, 10}, true⟩,
    .inr ⟨{5, 6, 8, 11}, true⟩,
    .inr ⟨{5, 6, 9, 10}, true⟩,
    .inr ⟨{5, 6, 9, 11}, true⟩,
    .inr ⟨{5, 7, 8, 10}, true⟩,
    .inr ⟨{5, 7, 8, 11}, true⟩,
    .inr ⟨{5, 7, 9, 10}, true⟩,
    .inr ⟨{5, 7, 9, 11}, true⟩,
    .inl ⟨![{0, 6, 7}, {1, 2, 3}, {4, 8, 9}, {5, 10, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 7}, {1, 2, 3}, {4, 10, 11}, {5, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 3}, {4, 6, 7}, {5, 10, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 3}, {4, 6, 10}, {5, 7, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 3}, {4, 7, 10}, {5, 6, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 3}, {4, 10, 11}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 6, 7}, {5, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 8, 9}, {5, 6, 7}], ![false, false, false, false]⟩]
theorem witnesses0_valid : ∀ i : Fin 27,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 496 16417)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_3_10
