import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_8_11.Clauses0500_0510
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_8_11
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses2 : Fin 11 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 10, 11}, {1, 6, 7}, {2, 3, 8}, {4, 5, 9}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 7}, {2, 3, 9}, {4, 5, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 7}, {2, 4, 9}, {3, 5, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 7}, {2, 5, 9}, {3, 4, 8}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 6, 8}, {2, 3, 7}, {4, 5, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 8}, {2, 3, 6}, {4, 5, 9}], ![false, true, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 8}, {2, 5, 6}, {3, 4, 9}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 9}, {2, 4, 6}, {3, 5, 8}], ![false, true, true, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 7, 9}, {2, 5, 8}, {3, 4, 6}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 10, 11}, {1, 8, 9}, {2, 3, 6}, {4, 5, 7}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 10, 11}, {1, 8, 9}, {2, 5, 6}, {3, 4, 7}], ![false, false, false, false]⟩]
theorem witnesses2_valid : ∀ i : Fin 11,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 787 24865)
      ((inputBlock2.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses2 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_8_11
