import MerLeanExperiment.NeighborhoodMeaningWitness
import MerLeanExperiment.Certificates.Z12Direct_3_1_1.Clauses0000_0005
namespace CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.Z12Direct_3_1_1
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses0 : Fin 6 → ColoringClauseWitness 12 4 ⊕ ForbiddenFourClauseWitness 12 :=
  ![
    .inl ⟨![{0, 2, 3}, {1, 8, 9}, {4, 7, 11}, {5, 6, 10}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 10}, {4, 6, 11}, {5, 7, 9}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 8, 11}, {4, 6, 10}, {5, 7, 9}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 10}, {4, 7, 11}, {5, 6, 8}], ![true, true, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 9, 11}, {4, 6, 10}, {5, 7, 8}], ![true, false, true, true]⟩,
    .inl ⟨![{0, 2, 3}, {1, 10, 11}, {4, 7, 9}, {5, 6, 8}], ![true, false, true, true]⟩]
theorem witnesses0_valid : ∀ i : Fin 6,
    ColoringOrForbiddenValid (neighborhoodPattern 12 3 4 206327905)
      ((inputBlock0.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      (witnesses0 i) := by
  decide +kernel
end CochromaticTwenty.NeighborhoodMeaning.Z12Direct_3_1_1
