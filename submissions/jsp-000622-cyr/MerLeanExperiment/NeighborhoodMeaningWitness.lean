import MerLeanExperiment.NeighborhoodPattern
import MerLeanExperiment.ColoringClauses

namespace CochromaticTwenty

def ColoringOrForbiddenValid {n k : ℕ} (p : GraphPattern n) (c : Std.Sat.CNF.Clause ℕ) :
    ColoringClauseWitness n k ⊕ ForbiddenFourClauseWitness n → Prop
  | .inl w => w.Valid p c
  | .inr w => w.Valid p c

instance instDecidableColoringOrForbiddenValid {n k : ℕ} (p : GraphPattern n)
    (c : Std.Sat.CNF.Clause ℕ)
    (w : ColoringClauseWitness n k ⊕ ForbiddenFourClauseWitness n) :
    Decidable (ColoringOrForbiddenValid p c w) := by
  cases w <;> simp only [ColoringOrForbiddenValid] <;> infer_instance

end CochromaticTwenty
