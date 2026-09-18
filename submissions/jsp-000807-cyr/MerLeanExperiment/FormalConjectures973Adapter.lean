import MerLeanExperiment.FormalConjectures973Frozen
import MerLeanExperiment.Statement

/-!
# Logical adapter for the frozen Formal Conjectures statement

This module records the transparent logical conversion between the independently
frozen, source-exact external theorem type `False ↔ Positive` and the local
target `¬ Positive`.  It makes no claim that the native Formal Conjectures
package or an official comparator program was run.
-/

namespace Erdos973

/-- The locally frozen expanded external type is exactly equivalent to the
candidate-independent target definition. -/
theorem formalConjectures973Expanded_iff_target :
    External.FormalConjectures973Expanded ↔ Target := by
  change (False ↔ Erdos973Positive) ↔ ¬ Erdos973Positive
  tauto

/-- Package a proof of the local target in the exact frozen external theorem
shape. -/
theorem formalConjectures973Expanded_of_target (h : Target) :
    External.FormalConjectures973Expanded :=
  formalConjectures973Expanded_iff_target.mpr h

end Erdos973
