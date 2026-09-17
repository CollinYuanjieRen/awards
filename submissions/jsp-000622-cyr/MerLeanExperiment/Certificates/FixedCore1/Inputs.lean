import MerLeanExperiment.Certificates.FixedCore1.Clauses0000_0249
import MerLeanExperiment.Certificates.FixedCore1.Clauses0250_0499
import MerLeanExperiment.Certificates.FixedCore1.Clauses0500_0749
import MerLeanExperiment.Certificates.FixedCore1.Clauses0750_0999
import MerLeanExperiment.Certificates.FixedCore1.Clauses1000_1249
import MerLeanExperiment.Certificates.FixedCore1.Clauses1250_1499
import MerLeanExperiment.Certificates.FixedCore1.Clauses1500_1749
import MerLeanExperiment.Certificates.FixedCore1.Clauses1750_1999
import MerLeanExperiment.Certificates.FixedCore1.Clauses2000_2249
import MerLeanExperiment.Certificates.FixedCore1.Clauses2250_2499
import MerLeanExperiment.Certificates.FixedCore1.Clauses2500_2749
import MerLeanExperiment.Certificates.FixedCore1.Clauses2750_2999
import MerLeanExperiment.Certificates.FixedCore1.Clauses3000_3249
import MerLeanExperiment.Certificates.FixedCore1.Clauses3250_3499
import MerLeanExperiment.Certificates.FixedCore1.Clauses3500_3749
import MerLeanExperiment.Certificates.FixedCore1.Clauses3750_3999
import MerLeanExperiment.Certificates.FixedCore1.Clauses4000_4249
import MerLeanExperiment.Certificates.FixedCore1.Clauses4250_4499
import MerLeanExperiment.Certificates.FixedCore1.Clauses4500_4749
import MerLeanExperiment.Certificates.FixedCore1.Clauses4750_4999
import MerLeanExperiment.Certificates.FixedCore1.Clauses5000_5249
import MerLeanExperiment.Certificates.FixedCore1.Clauses5250_5499
import MerLeanExperiment.Certificates.FixedCore1.Clauses5500_5749
import MerLeanExperiment.Certificates.FixedCore1.Clauses5750_5879

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through5880. -/
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
  | _ => DefaultClause.empty
def InputSat (a : PosFin 65 → Bool) : Prop :=
  ∀ i, i < 5880 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 65 := indexedFormula 5880 inputClause
def concreteCNF : CNF Nat := indexedCNF 5880 inputClause
/-- Input SHA256: 6c4c4cf91744a02b1b4be9dec2b74e904c7191bd4a0a6630d2367b3ba4264592; LRAT SHA256: 508d4b8faf4023d26bea738956ac3236d38dc4cb2fb3bbee22ad36eb546d8b80. -/
theorem initialFormula_supplies_inputs (a : PosFin 65 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 5880 inputClause a h

end CochromaticTwenty.Certificates.FixedCore1
