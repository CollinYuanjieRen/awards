import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_7_12.Clauses0250_0261
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_7_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_7_12
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 12 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 10, 11}, {1, 3, 4}, {2, 6, 9}, {5, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 4}, {2, 7, 8}, {5, 6, 9}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 4}, {2, 7, 9}, {5, 6, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 4}, {2, 8, 9}, {5, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 3, 9}, {2, 5, 8}, {4, 6, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 4, 6}, {2, 5, 7}, {3, 8, 9}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 5, 7}, {2, 6, 8}, {3, 4, 9}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 5, 9}, {2, 3, 8}, {4, 6, 7}], ![false, false, true, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 8}, {2, 4, 7}, {3, 5, 9}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 9}, {2, 4, 7}, {3, 5, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 9}, {2, 4, 6}, {3, 5, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 9}, {2, 4, 8}, {3, 5, 6}], ![false, true, true, true]⟩]
theorem witnesses1_valid : ∀ i : Fin 12,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 788 23137)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_7_12
