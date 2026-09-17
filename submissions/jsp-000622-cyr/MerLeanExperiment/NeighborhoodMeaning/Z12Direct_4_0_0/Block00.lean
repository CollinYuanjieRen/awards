import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_0_0.Clauses0000_0053
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_0_0
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 54 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 2, 3, 5}, false⟩,
    .inr ⟨{1, 3, 7, 11}, false⟩,
    .inr ⟨{1, 4, 5, 10}, false⟩,
    .inr ⟨{1, 4, 7, 11}, false⟩,
    .inr ⟨{2, 3, 5, 10}, false⟩,
    .inr ⟨{2, 3, 7, 10}, false⟩,
    .inr ⟨{2, 3, 7, 11}, false⟩,
    .inr ⟨{2, 4, 6, 11}, false⟩,
    .inr ⟨{2, 4, 7, 10}, false⟩,
    .inr ⟨{2, 4, 7, 11}, false⟩,
    .inr ⟨{2, 5, 9, 11}, true⟩,
    .inr ⟨{3, 4, 7, 8}, true⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 7}, {5, 9, 11}, {6, 8, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 7, 9}, {6, 8, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 9}, {2, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 6, 10}, {2, 7, 8}, {5, 9, 11}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 10, 11}, {2, 8, 9}, {5, 6, 7}], ![true, true, false, true]⟩,
    .inl ⟨![{0, 5, 8}, {1, 2, 9}, {3, 6, 11}, {4, 7, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 5, 8}, {1, 3, 6}, {2, 10, 11}, {4, 7, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 5, 8}, {1, 4, 6}, {2, 9, 11}, {3, 7, 10}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 5, 8}, {1, 4, 6}, {2, 10, 11}, {3, 7, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 5, 8}, {1, 4, 10}, {2, 7, 9}, {3, 6, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 5, 8}, {1, 6, 7}, {2, 10, 11}, {3, 4, 9}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 5, 8}, {1, 10, 11}, {2, 4, 6}, {3, 7, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 5, 8}, {1, 10, 11}, {2, 6, 7}, {3, 4, 9}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 5, 10}, {1, 2, 3}, {4, 9, 11}, {6, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 5, 10}, {1, 2, 4}, {3, 9, 11}, {6, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 5, 10}, {1, 2, 9}, {3, 6, 11}, {4, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 5, 10}, {1, 4, 6}, {2, 8, 9}, {3, 7, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 9}, {1, 3, 5}, {2, 8, 10}, {4, 7, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 6, 9}, {1, 3, 5}, {2, 10, 11}, {4, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 9}, {1, 5, 7}, {2, 10, 11}, {3, 4, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 6, 9}, {1, 10, 11}, {2, 5, 7}, {3, 4, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 8, 10}, {5, 7, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 8, 10}, {5, 7, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 10}, {1, 2, 3}, {4, 6, 8}, {5, 9, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 10}, {1, 2, 4}, {3, 6, 8}, {5, 9, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 10}, {1, 5, 6}, {2, 9, 11}, {3, 4, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 3}, {4, 5, 9}, {6, 8, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 4}, {3, 5, 9}, {6, 8, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 3}, {4, 10, 11}, {5, 6, 7}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 2, 4}, {3, 10, 11}, {5, 6, 7}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 3, 10}, {2, 4, 11}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 3, 11}, {2, 4, 10}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 4, 11}, {2, 3, 10}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 9}, {1, 5, 11}, {2, 3, 6}, {4, 7, 10}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 2, 3}, {4, 9, 10}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 2, 4}, {3, 9, 10}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 4, 6}, {2, 3, 10}, {5, 7, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 3}, {4, 8, 11}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 4}, {3, 8, 11}, {5, 6, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 11}, {2, 4, 5}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 6, 11}, {2, 5, 7}, {3, 4, 8}], ![false, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 54,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 32 480904)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_0_0
