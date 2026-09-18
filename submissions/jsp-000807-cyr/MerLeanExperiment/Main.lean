import MerLeanExperiment.UniformExteriorLowerBound
import MerLeanExperiment.Erdos973
import MerLeanExperiment.FormalConjectures973Adapter

/-!
# Complete negative answer to Erdős problem 973

This module exposes the complete catalog target after passing from the finite
analytic model to the original `Nat` family on `Icc 1 n`.
-/

namespace Erdos973

/-- Luo--Yang--Zhu's full eventual lower bound in the original sequence model. -/
theorem uniformExteriorLowerBound : UniformExteriorLowerBound :=
  uniformExteriorLowerBound_of_finite finiteUniformExteriorLowerBound

/-- The complete negative answer to Erdős problem 973. -/
theorem erdos973 : Target :=
  target_of_uniformExteriorLowerBound uniformExteriorLowerBound

/-- The complete result packaged in the independently frozen, source-exact
expanded Formal Conjectures theorem shape.  Native-package and official-program
execution status is recorded separately from this current-toolchain bridge. -/
theorem formalConjectures973Expanded :
    External.FormalConjectures973Expanded :=
  formalConjectures973Expanded_of_target erdos973

end Erdos973
