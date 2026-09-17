import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_0_2.Clauses0000_0062
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_0_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_0_2
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 63 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 4, 7, 9}, false⟩,
    .inr ⟨{1, 5, 7, 10}, true⟩,
    .inr ⟨{1, 5, 9, 10}, true⟩,
    .inr ⟨{2, 3, 7, 9}, false⟩,
    .inr ⟨{2, 4, 8, 10}, false⟩,
    .inr ⟨{2, 5, 7, 10}, true⟩,
    .inr ⟨{2, 5, 8, 11}, true⟩,
    .inr ⟨{2, 5, 9, 10}, true⟩,
    .inr ⟨{3, 4, 7, 10}, true⟩,
    .inr ⟨{3, 4, 7, 11}, true⟩,
    .inr ⟨{3, 4, 8, 9}, true⟩,
    .inr ⟨{3, 4, 9, 10}, true⟩,
    .inr ⟨{3, 6, 7, 8}, true⟩,
    .inr ⟨{3, 6, 7, 10}, true⟩,
    .inr ⟨{3, 7, 8, 11}, true⟩,
    .inr ⟨{4, 5, 6, 11}, false⟩,
    .inr ⟨{4, 6, 7, 8}, true⟩,
    .inr ⟨{4, 6, 7, 10}, true⟩,
    .inr ⟨{4, 7, 8, 11}, true⟩,
    .inr ⟨{5, 6, 7, 8}, true⟩,
    .inr ⟨{5, 6, 7, 10}, true⟩,
    .inr ⟨{5, 6, 9, 10}, true⟩,
    .inr ⟨{5, 7, 8, 11}, true⟩,
    .inl ⟨![{0, 1, 5}, {2, 3, 10}, {4, 7, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 1, 5}, {2, 10, 11}, {3, 4, 7}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 5}, {1, 3, 8}, {4, 7, 11}, {6, 9, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 9}, {5, 8, 11}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 3, 4}, {1, 2, 10}, {5, 7, 11}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 7, 8}, {5, 9, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 7, 9}, {5, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 7, 10}, {5, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 8, 9}, {5, 7, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 8, 10}, {5, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 3}, {4, 9, 10}, {5, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 7, 8}, {5, 9, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 7, 9}, {5, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 7, 10}, {5, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 8, 9}, {5, 7, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 8, 10}, {5, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 6, 11}, {1, 2, 4}, {3, 9, 10}, {5, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 6, 11}, {1, 8, 9}, {2, 5, 10}, {3, 4, 7}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 2, 3}, {4, 6, 8}, {5, 10, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 7, 9}, {1, 2, 3}, {4, 6, 11}, {5, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 9}, {1, 2, 3}, {4, 8, 10}, {5, 6, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 9}, {1, 2, 4}, {3, 6, 10}, {5, 8, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 2, 4}, {3, 6, 11}, {5, 8, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 7, 9}, {1, 3, 8}, {2, 5, 10}, {4, 6, 11}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 7, 9}, {1, 5, 8}, {2, 4, 6}, {3, 10, 11}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 3}, {4, 6, 11}, {5, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 3}, {4, 7, 9}, {5, 6, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 4}, {3, 6, 11}, {5, 7, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 4}, {3, 7, 9}, {5, 6, 11}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 3}, {4, 5, 8}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 3}, {4, 5, 10}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 4}, {3, 5, 8}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 4}, {3, 5, 10}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 5, 8}, {2, 6, 10}, {3, 4, 7}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 5, 7}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 5, 9}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 3}, {4, 6, 7}, {5, 8, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 4}, {3, 5, 7}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 4}, {3, 5, 9}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 2, 4}, {3, 8, 9}, {5, 6, 7}], ![false, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 63,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 224 25872)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_0_2
