import MerLeanExperiment.FixedCorePattern
import MerLeanExperiment.Certificates.FixedCore0.Clauses7500_7549
namespace CochromaticTwenty.FixedCore0Meaning
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.FixedCore0
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def pairBlock30 : Fin 50 → PairClauseWitness 20 :=
  ![
    ⟨{2, 11, 15, 17}, {3, 12, 14, 19}, true, true⟩,
    ⟨{2, 11, 15, 17}, {3, 14, 18, 19}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 4, 7, 14}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 5, 6, 7}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 5, 7, 8}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 5, 8, 10}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 5, 10, 14}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 5, 10, 16}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 6, 8, 14}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 7, 14, 16}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 8, 12, 14}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 8, 14, 16}, true, true⟩,
    ⟨{2, 11, 17, 19}, {3, 9, 14, 15}, true, false⟩,
    ⟨{2, 11, 17, 19}, {3, 14, 16, 18}, true, true⟩,
    ⟨{2, 12, 13, 17}, {3, 10, 18, 19}, true, true⟩,
    ⟨{2, 12, 14, 19}, {3, 4, 8, 18}, true, false⟩,
    ⟨{2, 12, 14, 19}, {3, 5, 7, 17}, true, false⟩,
    ⟨{2, 12, 14, 19}, {3, 6, 7, 9}, true, false⟩,
    ⟨{2, 12, 14, 19}, {3, 6, 10, 17}, true, true⟩,
    ⟨{2, 12, 14, 19}, {3, 15, 16, 18}, true, true⟩,
    ⟨{2, 12, 17, 19}, {3, 5, 9, 18}, true, true⟩,
    ⟨{2, 12, 17, 19}, {3, 5, 10, 14}, true, false⟩,
    ⟨{2, 12, 17, 19}, {3, 9, 14, 15}, true, false⟩,
    ⟨{2, 13, 15, 16}, {3, 5, 7, 17}, true, false⟩,
    ⟨{2, 13, 15, 16}, {3, 5, 11, 19}, true, true⟩,
    ⟨{2, 13, 15, 16}, {3, 5, 12, 19}, true, true⟩,
    ⟨{2, 13, 15, 16}, {3, 5, 18, 19}, true, true⟩,
    ⟨{2, 13, 15, 16}, {3, 7, 11, 19}, true, true⟩,
    ⟨{2, 13, 15, 16}, {3, 11, 12, 18}, true, false⟩,
    ⟨{2, 13, 15, 17}, {3, 5, 10, 14}, true, false⟩,
    ⟨{2, 13, 15, 17}, {3, 5, 12, 19}, true, true⟩,
    ⟨{2, 13, 15, 17}, {3, 7, 11, 19}, true, true⟩,
    ⟨{2, 13, 15, 17}, {3, 10, 18, 19}, true, true⟩,
    ⟨{2, 13, 15, 17}, {3, 11, 12, 18}, true, false⟩,
    ⟨{2, 14, 16, 18}, {3, 5, 7, 17}, true, false⟩,
    ⟨{2, 14, 16, 18}, {3, 6, 7, 12}, true, false⟩,
    ⟨{2, 14, 16, 18}, {3, 7, 10, 19}, true, true⟩,
    ⟨{2, 14, 16, 18}, {3, 10, 11, 12}, true, false⟩,
    ⟨{2, 14, 18, 19}, {3, 5, 6, 16}, true, false⟩,
    ⟨{2, 14, 18, 19}, {3, 5, 7, 17}, true, false⟩,
    ⟨{2, 14, 18, 19}, {3, 5, 10, 16}, true, false⟩,
    ⟨{2, 14, 18, 19}, {3, 6, 10, 17}, true, true⟩,
    ⟨{2, 14, 18, 19}, {3, 9, 10, 13}, true, true⟩,
    ⟨{2, 14, 18, 19}, {3, 10, 11, 12}, true, false⟩,
    ⟨{2, 14, 18, 19}, {3, 10, 12, 16}, true, false⟩,
    ⟨{2, 15, 16, 18}, {3, 5, 10, 14}, true, false⟩,
    ⟨{2, 15, 16, 18}, {3, 5, 12, 19}, true, true⟩,
    ⟨{2, 15, 16, 18}, {3, 7, 14, 19}, true, true⟩,
    ⟨{2, 15, 16, 18}, {3, 9, 10, 13}, true, true⟩,
    ⟨{2, 15, 16, 18}, {3, 12, 17, 19}, true, true⟩]
theorem pairBlock30_valid : ∀ i : Fin 50,
    (pairBlock30 i).Valid (fixedCorePattern coreCode0)
      ((inputBlock30.getD i.val DefaultClause.empty).clause.map
        (fun l => (l.1.val - 1, l.2))) := by
  decide +kernel
end CochromaticTwenty.FixedCore0Meaning
