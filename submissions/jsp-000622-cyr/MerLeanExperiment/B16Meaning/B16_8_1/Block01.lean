import MerLeanExperiment.B16Meaning.B16_8_1.Definitions
import MerLeanExperiment.Certificates.B16_8_1.Clauses0250_0287
namespace CochromaticTwenty.B16Meaning.B16_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.Certificates.B16_8_1
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def witnesses1 : Fin 38 → ForbiddenFourClauseWitness 16 ⊕ ℕ :=
  ![
    .inl ⟨{5, 8, 10, 15}, true⟩,
    .inl ⟨{5, 9, 10, 12}, true⟩,
    .inl ⟨{5, 9, 10, 14}, true⟩,
    .inl ⟨{5, 9, 11, 13}, true⟩,
    .inl ⟨{6, 7, 8, 9}, false⟩,
    .inl ⟨{6, 7, 8, 12}, false⟩,
    .inl ⟨{6, 7, 9, 15}, false⟩,
    .inl ⟨{6, 7, 10, 11}, false⟩,
    .inl ⟨{6, 7, 10, 13}, false⟩,
    .inl ⟨{6, 7, 11, 14}, false⟩,
    .inl ⟨{6, 7, 12, 13}, false⟩,
    .inl ⟨{6, 7, 12, 14}, false⟩,
    .inl ⟨{6, 7, 13, 15}, false⟩,
    .inl ⟨{6, 7, 14, 15}, false⟩,
    .inl ⟨{6, 8, 10, 14}, true⟩,
    .inl ⟨{6, 8, 10, 15}, true⟩,
    .inl ⟨{6, 8, 11, 13}, true⟩,
    .inl ⟨{6, 8, 11, 15}, true⟩,
    .inl ⟨{6, 8, 13, 14}, true⟩,
    .inl ⟨{6, 9, 10, 12}, true⟩,
    .inl ⟨{6, 9, 10, 14}, true⟩,
    .inl ⟨{6, 9, 11, 12}, true⟩,
    .inl ⟨{6, 9, 11, 13}, true⟩,
    .inl ⟨{6, 9, 13, 14}, true⟩,
    .inl ⟨{6, 10, 12, 15}, true⟩,
    .inl ⟨{6, 11, 12, 15}, true⟩,
    .inl ⟨{7, 8, 10, 14}, true⟩,
    .inl ⟨{7, 8, 10, 15}, true⟩,
    .inl ⟨{7, 8, 11, 13}, true⟩,
    .inl ⟨{7, 8, 11, 15}, true⟩,
    .inl ⟨{7, 8, 13, 14}, true⟩,
    .inl ⟨{7, 9, 10, 12}, true⟩,
    .inl ⟨{7, 9, 10, 14}, true⟩,
    .inl ⟨{7, 9, 11, 12}, true⟩,
    .inl ⟨{7, 9, 11, 13}, true⟩,
    .inl ⟨{7, 9, 13, 14}, true⟩,
    .inl ⟨{7, 10, 12, 15}, true⟩,
    .inl ⟨{7, 11, 12, 15}, true⟩]
theorem witnesses1_valid : ∀ i : Fin 38,
    ClassificationClauseValid (neighborhoodPattern 16 7 946323 206327905)
      ((inputBlock1.getD i.val DefaultClause.empty).clause.map (fun l => (l.1.val - 1, l.2)))
      allowedCodes (witnesses1 i) := by
  decide +kernel
end CochromaticTwenty.B16Meaning.B16_8_1
