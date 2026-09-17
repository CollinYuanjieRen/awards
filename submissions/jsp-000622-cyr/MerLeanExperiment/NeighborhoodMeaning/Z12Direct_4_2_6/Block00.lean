import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_2_6.Clauses0000_0021
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_2_6
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 22 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 5, 10, 11}, true⟩,
    .inr ⟨{2, 5, 10, 11}, true⟩,
    .inr ⟨{3, 5, 10, 11}, true⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 5}, {6, 8, 11}, {7, 9, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 10}, {5, 8, 11}, {6, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 11}, {5, 9, 10}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 5, 8}, {3, 10, 11}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 8, 11}, {3, 5, 10}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 10, 11}, {3, 5, 8}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 5}, {6, 8, 11}, {7, 9, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 8}, {5, 10, 11}, {6, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 8, 11}, {6, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 11}, {5, 9, 10}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 8}, {3, 10, 11}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 8, 11}, {3, 5, 10}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 10, 11}, {3, 5, 8}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 5}, {6, 8, 11}, {7, 9, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 8}, {5, 10, 11}, {6, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 8, 11}, {6, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 9, 10}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 8}, {2, 10, 11}, {6, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 8, 11}, {2, 5, 10}, {6, 7, 9}], ![true, true, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 22,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 56 666115)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_2_6
