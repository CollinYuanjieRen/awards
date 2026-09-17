import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_4_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c251 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c252 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c253 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c254 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨21, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c255 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c256 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c257 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c258 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c259 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c260 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c261 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c262 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c263 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c264 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c265 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c266 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c267 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c268 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c269 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c270 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c271 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨9, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c272 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c273 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def inputBlock1 : Array (DefaultClause 31) := #[c251, c252, c253, c254, c255, c256, c257, c258, c259, c260, c261, c262, c263, c264, c265, c266, c267, c268, c269, c270, c271, c272, c273]

end CochromaticTwenty.Certificates.Z12Direct_5_4_11
