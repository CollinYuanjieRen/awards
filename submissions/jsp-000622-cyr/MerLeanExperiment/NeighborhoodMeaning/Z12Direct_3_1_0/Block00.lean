import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_3_1_0.Clauses0000_0008
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_3_1_0
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 9 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 2, 3}, {1, 6, 7}, {4, 9, 10}, {5, 8, 11}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 6, 9}, {4, 7, 10}, {5, 8, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 6, 11}, {4, 9, 10}, {5, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 7, 8}, {4, 9, 10}, {5, 6, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 7, 10}, {4, 6, 9}, {5, 8, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 9}, {4, 7, 10}, {5, 6, 11}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 10}, {4, 5, 7}, {6, 9, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 11}, {4, 5, 6}, {7, 8, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 10, 11}, {4, 6, 9}, {5, 7, 8}], ![true, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 9,
    ColoringOrForbiddenValid (neighborhoodPattern 12 3 4 153315680)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_0
