import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_8_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c501 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c502 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c503 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c504 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c505 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c506 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c507 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c508 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c509 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c510 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c511 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c512 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c513 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c514 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c515 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c516 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c517 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c518 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c519 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c520 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c521 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c522 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c523 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨15, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c524 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c525 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c526 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c527 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c528 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c529 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c530 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def inputBlock2 : Array (DefaultClause 31) := #[c501, c502, c503, c504, c505, c506, c507, c508, c509, c510, c511, c512, c513, c514, c515, c516, c517, c518, c519, c520, c521, c522, c523, c524, c525, c526, c527, c528, c529, c530]

end CochromaticTwenty.Certificates.Z12Direct_5_8_4
