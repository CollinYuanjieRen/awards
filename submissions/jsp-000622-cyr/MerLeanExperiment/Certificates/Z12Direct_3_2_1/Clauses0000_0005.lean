import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_3_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 17 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c2 : DefaultClause 17 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c3 : DefaultClause 17 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c4 : DefaultClause 17 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c5 : DefaultClause 17 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c6 : DefaultClause 17 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 17) := #[c1, c2, c3, c4, c5, c6]

end CochromaticTwenty.Certificates.Z12Direct_3_2_1
