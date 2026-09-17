import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_6_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c2 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c3 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c4 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c5 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c6 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c7 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c8 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c9 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c10 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c11 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c12 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c13 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨15, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c14 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c15 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c16 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c17 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c18 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c19 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c20 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c21 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c22 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c23 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c24 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c25 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c26 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c27 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c28 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c29 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c30 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c31 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c32 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c33 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c34 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c35 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c36 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c37 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c38 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c39 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c40 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c41 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c42 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 31) := #[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42]

end CochromaticTwenty.Certificates.Z12Direct_5_6_10
