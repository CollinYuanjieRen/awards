import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_8_3.Clauses0250_0290
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_8_3
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 41 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 7, 9}, {1, 8, 10}, {2, 5, 11}, {3, 4, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 6}, {3, 4, 10}, {5, 8, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 10}, {3, 4, 8}, {5, 6, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 3, 9}, {2, 4, 10}, {5, 6, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 4, 9}, {2, 5, 10}, {3, 6, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 5, 9}, {2, 3, 6}, {4, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 11}, {1, 5, 9}, {2, 3, 10}, {4, 6, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 5, 10}, {2, 4, 8}, {3, 6, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 6, 9}, {2, 3, 10}, {4, 5, 8}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 6, 9}, {2, 5, 10}, {3, 4, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 6}, {3, 4, 9}, {5, 7, 11}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 7}, {3, 4, 11}, {5, 6, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 3, 6}, {2, 4, 7}, {5, 9, 11}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 3, 7}, {2, 9, 11}, {4, 5, 6}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 4, 7}, {2, 5, 9}, {3, 6, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 4, 9}, {2, 5, 7}, {3, 6, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 4, 11}, {2, 5, 6}, {3, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 5, 9}, {2, 3, 6}, {4, 7, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 5, 9}, {2, 4, 7}, {3, 6, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 5, 9}, {2, 6, 7}, {3, 4, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 6, 9}, {2, 5, 11}, {3, 4, 7}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 6, 11}, {2, 5, 9}, {3, 4, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 7, 9}, {2, 5, 11}, {3, 4, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 7, 11}, {2, 4, 9}, {3, 5, 6}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 4, 6}, {2, 3, 10}, {5, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 4, 9}, {2, 5, 7}, {3, 6, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 5, 7}, {2, 9, 10}, {3, 4, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 5, 9}, {2, 6, 7}, {3, 4, 10}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 7, 9}, {2, 5, 6}, {3, 4, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 7, 9}, {2, 5, 10}, {3, 4, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 9, 10}, {2, 3, 7}, {4, 5, 6}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 7}, {2, 6, 11}, {4, 5, 8}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 8}, {2, 4, 6}, {5, 7, 11}], ![false, true, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 3, 6}, {4, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 5, 11}, {2, 4, 6}, {3, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 7}, {2, 5, 11}, {3, 4, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 11}, {2, 4, 7}, {3, 5, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 7, 8}, {2, 3, 11}, {4, 5, 6}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 7, 8}, {2, 5, 6}, {3, 4, 11}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 7, 11}, {2, 4, 6}, {3, 5, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 8, 11}, {2, 5, 6}, {3, 4, 7}], ![false, false, false, false]⟩]
theorem witnesses1_valid : ∀ i : Fin 41,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 787 7952)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_3
