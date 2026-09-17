import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_4_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c251 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c252 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c253 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c254 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c255 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c256 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c257 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨26, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c258 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c259 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c260 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c261 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def inputBlock1 : Array (DefaultClause 31) := #[c251, c252, c253, c254, c255, c256, c257, c258, c259, c260, c261]

end CochromaticTwenty.Certificates.Z12Direct_5_4_9
