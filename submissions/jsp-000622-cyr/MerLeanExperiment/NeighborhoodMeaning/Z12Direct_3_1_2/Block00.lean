import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_3_1_2.Clauses0000_0011
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_3_1_2
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 12 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 2, 3}, {1, 4, 7}, {5, 9, 11}, {6, 8, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 4, 10}, {5, 9, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 4, 11}, {5, 7, 9}, {6, 8, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 5, 7}, {4, 9, 11}, {6, 8, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 5, 9}, {4, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 5, 10}, {4, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 6, 7}, {4, 8, 10}, {5, 9, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 6, 8}, {4, 10, 11}, {5, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 6, 11}, {4, 8, 10}, {5, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 9}, {4, 10, 11}, {5, 6, 7}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 10}, {4, 9, 11}, {5, 6, 7}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 11}, {4, 8, 10}, {5, 6, 7}], ![true, true, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 12,
    ColoringOrForbiddenValid (neighborhoodPattern 12 3 4 60117131)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_2
