import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_4_0_1.Clauses0000_0010
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_4_0_1
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 11 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inr ⟨{3, 4, 10, 11}, true⟩,
    .inl ⟨![{0, 6, 10}, {1, 2, 3}, {4, 9, 11}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 6, 10}, {1, 2, 4}, {3, 9, 11}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 3}, {4, 7, 9}, {5, 6, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 8, 10}, {1, 2, 4}, {3, 7, 9}, {5, 6, 11}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 3}, {4, 6, 11}, {5, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 3}, {4, 7, 11}, {5, 6, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 4}, {3, 6, 11}, {5, 7, 8}], ![false, false, true, true]⟩,
    .inl ⟨![{0, 9, 10}, {1, 2, 4}, {3, 7, 11}, {5, 6, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 3}, {4, 6, 10}, {5, 7, 8}], ![false, false, false, true]⟩,
    .inl ⟨![{0, 9, 11}, {1, 2, 4}, {3, 6, 10}, {5, 7, 8}], ![false, false, false, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 11,
    ColoringOrForbiddenValid (neighborhoodPattern 12 4 32 944196)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_4_0_1
