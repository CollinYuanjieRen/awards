import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_5_1.Clauses0000_0011
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_5_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_5_1
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 12 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 4, 6, 10}, false⟩,
    .inr ⟨{2, 3, 6, 10}, false⟩,
    .inl ⟨![{0, 1, 2}, {3, 4, 6}, {5, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 2}, {3, 4, 10}, {5, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 6}, {5, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 10}, {5, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 6}, {5, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 6}, {5, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 6}, {2, 3, 10}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 4, 10}, {2, 3, 6}, {5, 7, 8}], ![false, false, false, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 12,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 51 944196)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_5_1
