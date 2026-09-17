import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_3_1_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 9 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c2 : DefaultClause 9 := directClause [(⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c3 : DefaultClause 9 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c4 : DefaultClause 9 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c5 : DefaultClause 9 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c6 : DefaultClause 9 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 9) := #[c1, c2, c3, c4, c5, c6]

end CochromaticTwenty.Certificates.Z12Direct_3_1_1
