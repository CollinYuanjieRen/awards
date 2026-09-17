import MerLeanExperiment.Certificates.B16_3_2.Steps1000_1073

/-! Generated from the actual pinned b16_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem initialFormula_unsat : Unsatisfiable (PosFin 57) initialFormula := by
  intro a ha
  have h := derived1472 a (initialFormula_supplies_inputs a ha)
  change false = true at h
  contradiction

theorem concreteCNF_unsat : concreteCNF.Unsat :=
  indexedCNF_unsat 398 inputClause initialFormula_unsat

#print axioms initialFormula_unsat
#print axioms concreteCNF_unsat

end CochromaticTwenty.Certificates.B16_3_2
