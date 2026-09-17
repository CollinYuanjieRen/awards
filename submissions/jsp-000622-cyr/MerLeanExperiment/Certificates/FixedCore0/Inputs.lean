import MerLeanExperiment.Certificates.FixedCore0.Clauses0000_0249
import MerLeanExperiment.Certificates.FixedCore0.Clauses0250_0499
import MerLeanExperiment.Certificates.FixedCore0.Clauses0500_0749
import MerLeanExperiment.Certificates.FixedCore0.Clauses0750_0999
import MerLeanExperiment.Certificates.FixedCore0.Clauses1000_1249
import MerLeanExperiment.Certificates.FixedCore0.Clauses1250_1499
import MerLeanExperiment.Certificates.FixedCore0.Clauses1500_1749
import MerLeanExperiment.Certificates.FixedCore0.Clauses1750_1999
import MerLeanExperiment.Certificates.FixedCore0.Clauses2000_2249
import MerLeanExperiment.Certificates.FixedCore0.Clauses2250_2499
import MerLeanExperiment.Certificates.FixedCore0.Clauses2500_2749
import MerLeanExperiment.Certificates.FixedCore0.Clauses2750_2999
import MerLeanExperiment.Certificates.FixedCore0.Clauses3000_3249
import MerLeanExperiment.Certificates.FixedCore0.Clauses3250_3499
import MerLeanExperiment.Certificates.FixedCore0.Clauses3500_3749
import MerLeanExperiment.Certificates.FixedCore0.Clauses3750_3999
import MerLeanExperiment.Certificates.FixedCore0.Clauses4000_4249
import MerLeanExperiment.Certificates.FixedCore0.Clauses4250_4499
import MerLeanExperiment.Certificates.FixedCore0.Clauses4500_4749
import MerLeanExperiment.Certificates.FixedCore0.Clauses4750_4999
import MerLeanExperiment.Certificates.FixedCore0.Clauses5000_5249
import MerLeanExperiment.Certificates.FixedCore0.Clauses5250_5499
import MerLeanExperiment.Certificates.FixedCore0.Clauses5500_5749
import MerLeanExperiment.Certificates.FixedCore0.Clauses5750_5999
import MerLeanExperiment.Certificates.FixedCore0.Clauses6000_6249
import MerLeanExperiment.Certificates.FixedCore0.Clauses6250_6499
import MerLeanExperiment.Certificates.FixedCore0.Clauses6500_6749
import MerLeanExperiment.Certificates.FixedCore0.Clauses6750_6999
import MerLeanExperiment.Certificates.FixedCore0.Clauses7000_7249
import MerLeanExperiment.Certificates.FixedCore0.Clauses7250_7499
import MerLeanExperiment.Certificates.FixedCore0.Clauses7500_7549

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through7550. -/
def inputClause (id : Nat) : DefaultClause 65 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | 3 => inputBlock3.getD ((id - 1) % 250) DefaultClause.empty
  | 4 => inputBlock4.getD ((id - 1) % 250) DefaultClause.empty
  | 5 => inputBlock5.getD ((id - 1) % 250) DefaultClause.empty
  | 6 => inputBlock6.getD ((id - 1) % 250) DefaultClause.empty
  | 7 => inputBlock7.getD ((id - 1) % 250) DefaultClause.empty
  | 8 => inputBlock8.getD ((id - 1) % 250) DefaultClause.empty
  | 9 => inputBlock9.getD ((id - 1) % 250) DefaultClause.empty
  | 10 => inputBlock10.getD ((id - 1) % 250) DefaultClause.empty
  | 11 => inputBlock11.getD ((id - 1) % 250) DefaultClause.empty
  | 12 => inputBlock12.getD ((id - 1) % 250) DefaultClause.empty
  | 13 => inputBlock13.getD ((id - 1) % 250) DefaultClause.empty
  | 14 => inputBlock14.getD ((id - 1) % 250) DefaultClause.empty
  | 15 => inputBlock15.getD ((id - 1) % 250) DefaultClause.empty
  | 16 => inputBlock16.getD ((id - 1) % 250) DefaultClause.empty
  | 17 => inputBlock17.getD ((id - 1) % 250) DefaultClause.empty
  | 18 => inputBlock18.getD ((id - 1) % 250) DefaultClause.empty
  | 19 => inputBlock19.getD ((id - 1) % 250) DefaultClause.empty
  | 20 => inputBlock20.getD ((id - 1) % 250) DefaultClause.empty
  | 21 => inputBlock21.getD ((id - 1) % 250) DefaultClause.empty
  | 22 => inputBlock22.getD ((id - 1) % 250) DefaultClause.empty
  | 23 => inputBlock23.getD ((id - 1) % 250) DefaultClause.empty
  | 24 => inputBlock24.getD ((id - 1) % 250) DefaultClause.empty
  | 25 => inputBlock25.getD ((id - 1) % 250) DefaultClause.empty
  | 26 => inputBlock26.getD ((id - 1) % 250) DefaultClause.empty
  | 27 => inputBlock27.getD ((id - 1) % 250) DefaultClause.empty
  | 28 => inputBlock28.getD ((id - 1) % 250) DefaultClause.empty
  | 29 => inputBlock29.getD ((id - 1) % 250) DefaultClause.empty
  | 30 => inputBlock30.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 65 → Bool) : Prop :=
  ∀ i, i < 7550 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 65 := indexedFormula 7550 inputClause
def concreteCNF : CNF Nat := indexedCNF 7550 inputClause
/-- Input SHA256: 88df2e52bc1df063252284bf3d83a7fdc74f9d8c9ec330df991733900fd5243e; LRAT SHA256: 8758be61c0bd6e1e169ee4acf2102b1e7c9e6cd26556ec0f04870b9f10cb4eb0. -/
theorem initialFormula_supplies_inputs (a : PosFin 65 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 7550 inputClause a h

end CochromaticTwenty.Certificates.FixedCore0
