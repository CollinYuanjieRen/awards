import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_2_2.Clauses0000_0058
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_2_2
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 59 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 2, 3, 5}, false⟩,
    .inr ⟨{1, 2, 3, 6}, false⟩,
    .inr ⟨{1, 5, 6, 11}, true⟩,
    .inr ⟨{1, 5, 10, 11}, true⟩,
    .inr ⟨{2, 5, 10, 11}, true⟩,
    .inr ⟨{3, 5, 6, 11}, true⟩,
    .inr ⟨{3, 5, 10, 11}, true⟩,
    .inr ⟨{3, 6, 8, 9}, true⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 6}, {5, 10, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 7}, {5, 10, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 10}, {5, 6, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 3, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 5, 6}, {3, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 5, 7}, {3, 10, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 5, 10}, {3, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 5, 11}, {3, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 6, 11}, {3, 5, 10}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 7, 10}, {3, 5, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 10, 11}, {3, 5, 6}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 1, 4}, {2, 10, 11}, {3, 5, 7}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 6}, {5, 10, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 7}, {5, 10, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 6, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 6}, {3, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 7}, {3, 10, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 10}, {3, 6, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 11}, {3, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 6, 11}, {3, 5, 10}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 6, 11}, {3, 8, 9}, {5, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 10, 11}, {3, 5, 6}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 10, 11}, {3, 5, 7}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 6}, {5, 10, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 7}, {5, 10, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 6, 11}, {7, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 6}, {2, 10, 11}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 7}, {2, 10, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 11}, {2, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 6, 11}, {2, 5, 10}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 6, 11}, {2, 8, 9}, {5, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 7, 10}, {2, 5, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 10, 11}, {2, 5, 6}, {7, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 6, 7}, {1, 2, 3}, {4, 8, 9}, {5, 10, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 10}, {1, 2, 5}, {3, 4, 11}, {7, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 10}, {1, 3, 5}, {2, 4, 11}, {7, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 10}, {1, 4, 11}, {2, 3, 5}, {7, 8, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 5}, {3, 6, 7}, {4, 9, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 3, 5}, {2, 6, 7}, {4, 9, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 4, 11}, {2, 5, 9}, {3, 6, 7}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 4, 11}, {2, 6, 7}, {3, 5, 9}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 6, 7}, {2, 3, 5}, {4, 9, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 6, 7}, {2, 4, 11}, {3, 5, 9}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 5}, {3, 6, 7}, {4, 8, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 5}, {2, 6, 7}, {4, 8, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 11}, {2, 5, 8}, {3, 6, 7}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 11}, {2, 6, 7}, {3, 5, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 7}, {2, 3, 5}, {4, 8, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 7}, {2, 4, 11}, {3, 5, 8}], ![false, false, true, false]⟩]
theorem witnesses0_valid : ∀ i : Fin 59,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 56 944204)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_2_2
