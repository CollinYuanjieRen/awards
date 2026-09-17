import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_2_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 1 := directClause [] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 1) := #[c1]

end CochromaticTwenty.Certificates.Z12Direct_5_2_8
