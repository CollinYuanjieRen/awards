import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_4_9.Clauses0250_0260
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_4_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_4_9
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 11 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 9, 11}, {1, 2, 8}, {3, 4, 10}, {5, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 8}, {2, 4, 6}, {5, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 10}, {2, 4, 8}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 3, 10}, {2, 7, 8}, {4, 5, 6}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 7}, {2, 6, 8}, {3, 5, 10}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 7}, {2, 8, 10}, {3, 5, 6}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 5, 7}, {3, 6, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 6, 8}, {3, 5, 7}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 6}, {2, 3, 10}, {4, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 7}, {2, 3, 10}, {4, 6, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 7, 8}, {2, 5, 10}, {3, 4, 6}], ![false, true, true, true]⟩]
theorem witnesses1_valid : ∀ i : Fin 11,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 424 15169)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_4_9
