import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_8_14.Clauses0500_0529
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_8_14
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses2 : Fin 30 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 6, 8}, {3, 4, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 7}, {2, 5, 8}, {3, 4, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 8}, {2, 4, 11}, {3, 5, 7}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 6}, {3, 4, 7}, {5, 8, 10}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 7}, {3, 4, 10}, {5, 6, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 7}, {2, 4, 10}, {5, 6, 8}], ![false, true, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 7}, {2, 5, 6}, {4, 8, 10}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 7}, {2, 6, 10}, {4, 5, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 8}, {2, 4, 7}, {5, 6, 10}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 10}, {2, 5, 7}, {4, 6, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 6}, {2, 5, 7}, {3, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 6}, {2, 5, 8}, {3, 7, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 3, 6}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 3, 7}, {5, 6, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 5, 7}, {3, 6, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 6, 7}, {3, 5, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 3, 7}, {4, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 3, 8}, {4, 7, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 4, 8}, {3, 7, 10}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 7, 8}, {3, 4, 10}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 8, 10}, {3, 4, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 10}, {2, 3, 8}, {4, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 10}, {2, 6, 7}, {3, 4, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 10}, {2, 6, 8}, {3, 4, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 10}, {2, 7, 8}, {3, 4, 6}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 7, 8}, {2, 3, 6}, {4, 5, 10}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 7, 10}, {2, 3, 8}, {4, 5, 6}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 7, 10}, {2, 5, 8}, {3, 4, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 8, 10}, {2, 3, 6}, {4, 5, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 8, 10}, {2, 4, 7}, {3, 5, 6}], ![false, false, true, true]⟩]
theorem witnesses2_valid : ∀ i : Fin 30,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 787 15243)
      ((inputBlock2.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses2 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_14
