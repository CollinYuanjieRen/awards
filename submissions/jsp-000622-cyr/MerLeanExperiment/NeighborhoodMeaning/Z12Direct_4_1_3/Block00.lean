import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_1_3.Clauses0000_0043
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_1_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_1_3
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 44 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 4, 5, 6}, false⟩,
    .inr ⟨{1, 5, 7, 10}, true⟩,
    .inr ⟨{1, 5, 9, 11}, true⟩,
    .inr ⟨{1, 5, 10, 11}, true⟩,
    .inr ⟨{2, 4, 9, 11}, true⟩,
    .inr ⟨{2, 4, 10, 11}, true⟩,
    .inr ⟨{3, 4, 9, 11}, true⟩,
    .inr ⟨{3, 4, 10, 11}, true⟩,
    .inr ⟨{3, 5, 7, 10}, true⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 9}, {5, 10, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 10}, {5, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 3, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 9}, {3, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 5, 11}, {3, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 6, 9}, {3, 10, 11}, {5, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 6, 10}, {3, 7, 11}, {5, 8, 9}], ![true, true, false, true]⟩,
    .inl ⟨![{0, 2, 4}, {1, 9, 11}, {3, 5, 10}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 8}, {5, 9, 11}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 9}, {5, 10, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 11}, {5, 8, 9}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 9}, {2, 10, 11}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 5, 11}, {2, 7, 10}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 6, 9}, {2, 10, 11}, {5, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 6, 10}, {2, 7, 11}, {5, 8, 9}], ![true, true, false, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 10, 11}, {2, 5, 7}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 7, 10}, {5, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 9, 10}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 4, 7}, {2, 3, 10}, {5, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 4, 10}, {2, 3, 7}, {5, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 6, 8}, {2, 5, 10}, {3, 4, 11}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 6, 10}, {2, 5, 8}, {3, 4, 11}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 8, 11}, {2, 3, 10}, {4, 5, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 3}, {4, 6, 10}, {5, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 4, 5}, {2, 3, 10}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 8, 9}, {2, 3, 10}, {4, 5, 6}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 11}, {1, 2, 3}, {4, 6, 9}, {5, 7, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 9, 10}, {2, 3, 7}, {4, 5, 6}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 3}, {4, 5, 11}, {6, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 3}, {4, 6, 11}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 5}, {3, 4, 11}, {6, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 5}, {2, 4, 11}, {6, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 4, 5}, {2, 3, 11}, {6, 7, 8}], ![false, false, false, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 44,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 48 483585)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_1_3
