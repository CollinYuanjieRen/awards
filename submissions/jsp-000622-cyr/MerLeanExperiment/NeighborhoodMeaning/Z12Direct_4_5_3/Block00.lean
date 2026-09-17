import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_5_3.Clauses0000_0011
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_5_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_5_3
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 12 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 4, 9, 10}, false⟩,
    .inr ⟨{2, 3, 9, 10}, false⟩,
    .inl ⟨![{0, 1, 2}, {3, 4, 9}, {5, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 2}, {3, 4, 10}, {5, 9, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 9}, {5, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 10}, {5, 9, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 9}, {5, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 9, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 9}, {5, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 9, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 4, 9}, {2, 3, 10}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 4, 10}, {2, 3, 9}, {5, 7, 8}], ![false, false, false, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 12,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 51 483585)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_5_3
