import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_4_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c2 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c3 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c4 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c5 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c6 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c7 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c8 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c9 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c10 : DefaultClause 29 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c11 : DefaultClause 29 := directClause [(⟨24, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c12 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c13 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c14 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 29) := #[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14]

end CochromaticTwenty.Certificates.Z12Direct_4_2_1
