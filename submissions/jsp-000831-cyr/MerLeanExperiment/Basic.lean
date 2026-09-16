import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
Definitions for Kesten's interval characterization (JSP-000831 / Erdős 998).
The count and eventual boundedness conventions follow plby/lean-proofs,
ErdosProblems/Erdos998.lean (Apache-2.0; formal authors Codex and GPT-5.6 Sol).
The main target is the length criterion, not the erroneous separate-endpoints claim.
-/

namespace Kesten

/-- Visits at times `1, ..., n` to the half-open interval `[u,v)`. -/
noncomputable def countInIco (α u v : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun j ↦
    u ≤ Int.fract (α * (j + 1 : ℕ)) ∧ Int.fract (α * (j + 1 : ℕ)) < v).card

/-- The counting discrepancy is eventually bounded by a nonnegative constant. -/
def HasBoundedRemainder (α u v : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(countInIco α u v n : ℝ) - (n : ℝ) * (v - u)| ≤ C

/-- Indicator of the interval evaluated at the circle representative in `[0,1)`. -/
noncomputable def intervalIndicator (u v : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  if u ≤ (AddCircle.equivIco 1 0 x : ℝ) ∧
      (AddCircle.equivIco 1 0 x : ℝ) < v then 1 else 0

end Kesten
