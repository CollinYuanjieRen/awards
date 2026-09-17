import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_3_5.Clauses0000_0040
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_3_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_3_5
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 41 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 2, 5, 6}, false⟩,
    .inr ⟨{1, 4, 10, 11}, false⟩,
    .inr ⟨{1, 5, 9, 10}, true⟩,
    .inr ⟨{1, 6, 9, 10}, true⟩,
    .inr ⟨{2, 3, 9, 11}, false⟩,
    .inr ⟨{2, 3, 10, 11}, false⟩,
    .inr ⟨{2, 5, 7, 11}, true⟩,
    .inr ⟨{2, 5, 9, 10}, true⟩,
    .inr ⟨{2, 6, 7, 11}, true⟩,
    .inr ⟨{2, 6, 9, 10}, true⟩,
    .inr ⟨{3, 5, 8, 11}, true⟩,
    .inr ⟨{3, 5, 9, 10}, true⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 9}, {5, 7, 10}, {6, 8, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 9}, {5, 8, 11}, {6, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 10}, {5, 7, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 10}, {5, 8, 9}, {6, 7, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 4, 11}, {5, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 3}, {2, 5, 7}, {4, 10, 11}, {6, 8, 9}], ![true, true, false, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 9}, {5, 7, 10}, {6, 8, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 9}, {5, 8, 11}, {6, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 7, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 8, 9}, {6, 7, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 11}, {5, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 7, 10}, {3, 5, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 8, 10}, {3, 6, 9}, {5, 7, 11}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 8, 11}, {3, 6, 9}, {5, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 7}, {5, 8, 11}, {6, 9, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 7}, {5, 9, 10}, {6, 8, 11}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 9}, {5, 7, 10}, {6, 8, 11}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 7, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 7, 10}, {2, 5, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 7, 10}, {2, 6, 11}, {5, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 7, 11}, {2, 5, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 7, 11}, {2, 6, 10}, {5, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 7, 8}, {1, 4, 9}, {2, 5, 6}, {3, 10, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 8}, {1, 4, 10}, {2, 5, 6}, {3, 9, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 8}, {1, 4, 11}, {2, 3, 5}, {6, 9, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 4, 10}, {2, 3, 5}, {6, 8, 11}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 4, 10}, {2, 3, 6}, {5, 8, 11}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 4, 11}, {2, 5, 6}, {3, 8, 10}], ![false, false, false, false]⟩]
theorem witnesses0_valid : ∀ i : Fin 41,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 50 1581345)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_3_5
