import MerLeanExperiment.CertificateKernel

/-! Generated from the actual pinned z12direct_5_0_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c251 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c252 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c253 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨11, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def c254 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def inputBlock1 : Array (DefaultClause 31) := #[c251, c252, c253, c254]

end CochromaticTwenty.Certificates.Z12Direct_5_0_13
