import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_8_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c501 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c502 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c503 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c504 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c505 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c506 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c507 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c508 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c509 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c510 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c511 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock2 : Array (DefaultClause 31) := #[c501, c502, c503, c504, c505, c506, c507, c508, c509, c510, c511]

end CochromaticTwenty.Certificates.Z12Direct_5_8_11
