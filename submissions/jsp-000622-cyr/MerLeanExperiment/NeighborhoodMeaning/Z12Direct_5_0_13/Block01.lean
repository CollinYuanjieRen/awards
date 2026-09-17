import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_0_13.Clauses0250_0253
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_0_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_0_13
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 4 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 9, 11}, {1, 5, 10}, {2, 4, 7}, {3, 6, 8}], ![false, true, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 6, 8}, {2, 4, 7}, {3, 5, 10}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 6, 8}, {2, 4, 10}, {3, 5, 7}], ![false, false, false, false]⟩,
    .inl ⟨![{0, 9, 11}, {1, 8, 10}, {2, 5, 6}, {3, 4, 7}], ![false, true, true, true]⟩]
theorem witnesses1_valid : ∀ i : Fin 4,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 224 12931)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_0_13
