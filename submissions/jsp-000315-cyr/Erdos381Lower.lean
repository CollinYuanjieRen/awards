import Erdos381Lower.Defs
import Erdos381Lower.Trial
import Erdos381Lower.Structure
import Erdos381Lower.Blocks
import Erdos381Lower.Dirichlet
import Erdos381Lower.GapCore
import Erdos381Lower.Gap
import Erdos381Lower.Counting

/-!
# Erdős #381 (JSP-000315): the growth of the highly composite counting function

Erdős (1944) lower bound `Q(N) ≥ (log N)^{1+c}`, proved here, together with Nicolas's (1971)
polynomial upper bound `Erdos381.NicolasPolynomialUpperBound`, proved in plby/lean-proofs.
The frozen faces of `challenge/Target.lean` are discharged below under the same names.
-/

namespace Erdos381Lower

open Erdos381 Filter

/-- Erdős 1944: `Q(N) ≥ (log N)^{1+c}` for all large `N`. -/
theorem erdos381_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ) :=
  erdos381_lower_of_gap erdos381_gap

/-- Erdős 1944 in `IsBigO` form. -/
theorem erdos381_lower_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ (1 + c)) =O[atTop] (fun N : ℕ ↦ (Q N : ℝ)) :=
  erdos381_lower_isBigO_of_gap erdos381_gap

/-- The two-sided growth statement: Erdős's lower bound together with Nicolas's polynomial upper
bound (`Erdos381.NicolasPolynomialUpperBound`, plby/lean-proofs). -/
theorem erdos381_two_sided :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ)) ∧
      NicolasPolynomialUpperBound :=
  erdos381_two_sided_of_gap erdos381_gap

end Erdos381Lower
