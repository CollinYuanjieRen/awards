import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_5_2_12.Clauses0000_0000
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_2_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_5_2_12
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 1 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 4, 5}, {1, 2, 3}, {6, 9, 11}, {7, 8, 10}], ![true, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 1,
    ColoringOrForbiddenValid (neighborhoodPattern 12 5 784 23137)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_5_2_12
