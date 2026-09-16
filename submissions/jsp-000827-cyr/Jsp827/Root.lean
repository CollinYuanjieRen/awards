import Jsp827.Statement
import Jsp827.Marstrand.Main

/-!
# Roots of the JSP-000827 / Erdős #994 development

**Target (Marstrand 1970).**  Khintchine's conjecture is false: there is a measurable
`E ⊆ (0,1)` for which the visit averages `(1/n) ∑_{k ≤ n} 1_E({kα})` fail to converge to
`λ(E)` for almost every `α`.
-/

namespace Erdos994

open MeasureTheory Set

/-- Explicit witness form: a measurable `E ⊆ (0,1)` with `∀ᵐ α, ¬ HasExpectedLimit E α`. -/
theorem exists_counterexample_ae :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ α : ℝ, ¬ HasExpectedLimit E α :=
  exists_counterexample_ae'

/-- **Marstrand's theorem:** the fixed-set Khintchine conjecture (`KhintchineFixedSet`,
the exact predicate of plby/lean-proofs `Erdos994`) is false. -/
theorem not_khintchineFixedSet : ¬ KhintchineFixedSet :=
  not_khintchineFixedSet_of_exists exists_counterexample_ae

end Erdos994
