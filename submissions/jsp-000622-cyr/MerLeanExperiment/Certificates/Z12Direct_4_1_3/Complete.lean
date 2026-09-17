import MerLeanExperiment.Certificates.Z12Direct_4_1_3.Steps0000_0015

/-! Generated from the actual pinned z12direct_4_1_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initialFormula_unsat : Unsatisfiable (PosFin 29) initialFormula := by
  intro a ha
  have h := derived60 a (initialFormula_supplies_inputs a ha)
  change false = true at h
  contradiction

theorem concreteCNF_unsat : concreteCNF.Unsat :=
  indexedCNF_unsat 44 inputClause initialFormula_unsat

#print axioms initialFormula_unsat
#print axioms concreteCNF_unsat

end CochromaticTwenty.Certificates.Z12Direct_4_1_3
