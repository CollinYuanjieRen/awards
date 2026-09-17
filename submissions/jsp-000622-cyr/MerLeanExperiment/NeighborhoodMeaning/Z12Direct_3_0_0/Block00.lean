import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_3_0_0.Clauses0000_0000
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_3_0_0
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 1 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 6, 7}, {1, 2, 3}, {4, 9, 10}, {5, 8, 11}], ![false, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 1,
    ColoringOrForbiddenValid (neighborhoodPattern 12 3 0 153315680)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_0_0
