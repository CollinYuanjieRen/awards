import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_4_2_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1 : DefaultClause 22 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c2 : DefaultClause 22 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c3 : DefaultClause 22 := directClause [(⟨15, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c4 : DefaultClause 22 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c5 : DefaultClause 22 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c6 : DefaultClause 22 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c7 : DefaultClause 22 := directClause [(⟨8, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c8 : DefaultClause 22 := directClause [(⟨11, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c9 : DefaultClause 22 := directClause [(⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c10 : DefaultClause 22 := directClause [(⟨1, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c11 : DefaultClause 22 := directClause [(⟨4, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c12 : DefaultClause 22 := directClause [(⟨6, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c13 : DefaultClause 22 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c14 : DefaultClause 22 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c15 : DefaultClause 22 := directClause [(⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c16 : DefaultClause 22 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c17 : DefaultClause 22 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c18 : DefaultClause 22 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c19 : DefaultClause 22 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c20 : DefaultClause 22 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c21 : DefaultClause 22 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def c22 : DefaultClause 22 := directClause [(⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def inputBlock0 : Array (DefaultClause 22) := #[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22]

end CochromaticTwenty.Certificates.Z12Direct_4_2_6
