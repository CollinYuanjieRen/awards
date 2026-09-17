import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_6_3.Clauses0000_0045
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_6_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_6_3
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 46 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{1, 2, 5, 8}, false⟩,
    .inr ⟨{1, 3, 5, 8}, false⟩,
    .inr ⟨{1, 4, 7, 11}, false⟩,
    .inr ⟨{1, 4, 8, 10}, false⟩,
    .inr ⟨{2, 3, 9, 11}, true⟩,
    .inr ⟨{2, 3, 10, 11}, true⟩,
    .inr ⟨{4, 5, 8, 9}, true⟩,
    .inr ⟨{4, 5, 9, 11}, true⟩,
    .inr ⟨{4, 5, 10, 11}, true⟩,
    .inl ⟨![{0, 2, 3}, {1, 4, 9}, {5, 10, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 4, 10}, {5, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 4, 11}, {5, 8, 9}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 5, 8}, {4, 9, 11}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 5, 11}, {4, 7, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 7, 10}, {4, 5, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 7, 11}, {4, 5, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 9}, {4, 5, 11}, {6, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 11}, {4, 5, 9}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 10}, {4, 5, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 11}, {4, 5, 10}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 10, 11}, {4, 5, 9}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 2, 9}, {3, 10, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 3, 9}, {2, 10, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 3, 10}, {2, 9, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 7, 10}, {2, 3, 11}, {6, 8, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 7, 11}, {2, 3, 10}, {6, 8, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 8, 9}, {2, 3, 11}, {6, 7, 10}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 8, 11}, {2, 3, 9}, {6, 7, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 9, 10}, {2, 3, 11}, {6, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 9, 11}, {2, 3, 10}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 4, 5}, {1, 10, 11}, {2, 3, 9}, {6, 7, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 4, 6}, {2, 3, 8}, {5, 10, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 9}, {1, 5, 8}, {2, 3, 11}, {4, 6, 10}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 4}, {3, 5, 10}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 2, 5}, {3, 4, 10}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 3, 4}, {2, 5, 10}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 3, 5}, {2, 4, 10}, {6, 8, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 7, 11}, {1, 6, 9}, {2, 3, 8}, {4, 5, 10}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 2, 4}, {3, 5, 9}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 2, 5}, {3, 4, 9}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 3, 4}, {2, 5, 9}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 11}, {1, 3, 5}, {2, 4, 9}, {6, 7, 10}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 4}, {3, 5, 11}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 5}, {3, 4, 11}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 4}, {2, 5, 11}, {6, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 3, 5}, {2, 4, 11}, {6, 7, 8}], ![false, false, false, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 46,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 516 7952)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_6_3
