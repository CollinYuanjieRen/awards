import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_3_12.Clauses0250_0290
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_3_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_3_12
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 41 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 9, 10}, {1, 2, 7}, {3, 8, 11}, {4, 5, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 8}, {3, 4, 11}, {5, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 8}, {3, 5, 11}, {4, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 8}, {3, 6, 7}, {4, 5, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 8}, {3, 6, 11}, {4, 5, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 8}, {3, 7, 11}, {4, 5, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 8}, {2, 5, 11}, {4, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 7}, {2, 3, 8}, {5, 6, 11}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 8}, {2, 3, 7}, {5, 6, 11}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 8}, {2, 3, 11}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 8}, {2, 5, 11}, {3, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 8}, {2, 6, 7}, {3, 5, 11}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 6}, {2, 3, 7}, {4, 8, 11}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 8}, {2, 3, 7}, {4, 6, 11}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 3, 6}, {4, 7, 8}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 3, 7}, {4, 6, 8}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 3, 8}, {4, 6, 7}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 7}, {2, 3, 11}, {4, 5, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 8}, {2, 5, 11}, {3, 4, 7}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 11}, {2, 3, 7}, {4, 5, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 7, 8}, {2, 3, 11}, {4, 5, 6}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 8, 11}, {2, 3, 7}, {4, 5, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 6, 7}, {5, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 6, 8}, {5, 7, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 7, 9}, {5, 6, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 8, 9}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 7}, {3, 4, 6}, {5, 8, 9}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 8}, {3, 6, 7}, {4, 5, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 6}, {2, 8, 9}, {4, 5, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 8}, {2, 6, 7}, {4, 5, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 4, 6}, {2, 3, 7}, {5, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 4, 7}, {2, 3, 6}, {5, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 4, 8}, {2, 3, 9}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 4, 9}, {2, 3, 8}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 5, 9}, {2, 6, 8}, {3, 4, 7}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 7}, {2, 3, 9}, {4, 5, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 8}, {2, 4, 7}, {3, 5, 9}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 9}, {2, 3, 7}, {4, 5, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 8}, {2, 3, 9}, {4, 5, 6}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 9}, {2, 5, 8}, {3, 4, 6}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 8, 9}, {2, 3, 7}, {4, 5, 6}], ![false, false, false, false]⟩]
theorem witnesses1_valid : ∀ i : Fin 41,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 496 23137)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_3_12
