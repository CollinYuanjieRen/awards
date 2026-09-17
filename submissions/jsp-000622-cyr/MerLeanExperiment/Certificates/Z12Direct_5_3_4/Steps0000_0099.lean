import MerLeanExperiment.Certificates.Z12Direct_5_3_4.Inputs

/-! Generated from the actual pinned z12direct_5_3_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c211 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c77, some c58, some c2, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked211 : lratChecker f211 p211 = .success := by decide +kernel
theorem unsat211 : Unsatisfiable (PosFin 31) f211 := by
  apply lratCheckerSound f211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p211
  · intro a ha; simp [p211] at ha; subst a; trivial
  · exact checked211
theorem derived211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c211 := by
  apply localUnsat_implies_entails f211 [c77, c58, c2] c211 unsat211 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c212 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c36, some c211, some c54, some c72, some c67, some c84, some c209, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked212 : lratChecker f212 p212 = .success := by decide +kernel
theorem unsat212 : Unsatisfiable (PosFin 31) f212 := by
  apply lratCheckerSound f212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p212
  · intro a ha; simp [p212] at ha; subst a; trivial
  · exact checked212
theorem derived212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c212 := by
  apply localUnsat_implies_entails f212 [c36, c211, c54, c72, c67, c84, c209] c212 unsat212 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c211 := derived211 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c213 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c32, some c31, some c114, some c129, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked213 : lratChecker f213 p213 = .success := by decide +kernel
theorem unsat213 : Unsatisfiable (PosFin 31) f213 := by
  apply lratCheckerSound f213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p213
  · intro a ha; simp [p213] at ha; subst a; trivial
  · exact checked213
theorem derived213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c213 := by
  apply localUnsat_implies_entails f213 [c32, c31, c114, c129] c213 unsat213 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c214 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c76, some c80, some c83, some c71, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked214 : lratChecker f214 p214 = .success := by decide +kernel
theorem unsat214 : Unsatisfiable (PosFin 31) f214 := by
  apply lratCheckerSound f214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p214
  · intro a ha; simp [p214] at ha; subst a; trivial
  · exact checked214
theorem derived214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c214 := by
  apply localUnsat_implies_entails f214 [c41, c76, c80, c83, c71] c214 unsat214 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c215 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c73, some c16, some c4, some c32, some c31, some c213, some c23, some c110, some c60, some c119, some c71, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked215 : lratChecker f215 p215 = .success := by decide +kernel
theorem unsat215 : Unsatisfiable (PosFin 31) f215 := by
  apply lratCheckerSound f215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p215
  · intro a ha; simp [p215] at ha; subst a; trivial
  · exact checked215
theorem derived215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c215 := by
  apply localUnsat_implies_entails f215 [c214, c73, c16, c4, c32, c31, c213, c23, c110, c60, c119, c71] c215 unsat215 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c213 := derived213 a h
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c216 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c32, some c110, some c115, some c119, some c106, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked216 : lratChecker f216 p216 = .success := by decide +kernel
theorem unsat216 : Unsatisfiable (PosFin 31) f216 := by
  apply lratCheckerSound f216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p216
  · intro a ha; simp [p216] at ha; subst a; trivial
  · exact checked216
theorem derived216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c216 := by
  apply localUnsat_implies_entails f216 [c32, c110, c115, c119, c106] c216 unsat216 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c217 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c215, some c216, some c4, some c87, some c76, some c82, some c79, some c71, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked217 : lratChecker f217 p217 = .success := by decide +kernel
theorem unsat217 : Unsatisfiable (PosFin 31) f217 := by
  apply lratCheckerSound f217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p217
  · intro a ha; simp [p217] at ha; subst a; trivial
  · exact checked217
theorem derived217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c217 := by
  apply localUnsat_implies_entails f217 [c214, c215, c216, c4, c87, c76, c82, c79, c71] c217 unsat217 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c215 := derived215 a h
  have h2 : Entails.eval a c216 := derived216 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c218 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c17, some c71, some c106, some c79, some c113, some c5, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked218 : lratChecker f218 p218 = .success := by decide +kernel
theorem unsat218 : Unsatisfiable (PosFin 31) f218 := by
  apply lratCheckerSound f218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p218
  · intro a ha; simp [p218] at ha; subst a; trivial
  · exact checked218
theorem derived218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c218 := by
  apply localUnsat_implies_entails f218 [c17, c71, c106, c79, c113, c5] c218 unsat218 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c219 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c17, some c218, some c82, some c118, some c5, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c17, c218, c82, c118, c5] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c218 := derived218 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c98, some c62, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c98, c62] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c4, some c5, some c124, some c63, some c43, some c97, some c94, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c4, c5, c124, c63, c43, c97, c94] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c51, some c154, some c182, some c141, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c217, c51, c154, c182, c141] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c219, some c217, some c51, some c5, some c221, some c32, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c222, c219, c217, c51, c5, c221, c32] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c219 := derived219 a h
  have h2 : Entails.eval a c217 := derived217 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c221 := derived221 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c219, some c217, some c51, some c223, some c41, some c4, some c91, some c32, some c68, some c43, some c129, some c127, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c222, c219, c217, c51, c223, c41, c4, c91, c32, c68, c43, c129, c127] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c219 := derived219 a h
  have h2 : Entails.eval a c217 := derived217 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c223 := derived223 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c119, some c83, some c4, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c119, c83, c4] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c219, some c224, some c225, some c71, some c106, some c80, some c115, some c4, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c219, c224, c225, c71, c106, c80, c115, c4] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c219 := derived219 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c4, some c101, some c80, some c89, some c1, some c125, some c66, some c57, some c69, some c59, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c226, c205, c4, c101, c80, c89, c1, c125, c66, c57, c69, c59] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c228 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c227, some c135, some c115, some c1, some c122, some c80, some c60, some c92, some c61, some c57, some c70, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked228 : lratChecker f228 p228 = .success := by decide +kernel
theorem unsat228 : Unsatisfiable (PosFin 31) f228 := by
  apply lratCheckerSound f228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p228
  · intro a ha; simp [p228] at ha; subst a; trivial
  · exact checked228
theorem derived228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c228 := by
  apply localUnsat_implies_entails f228 [c226, c205, c227, c135, c115, c1, c122, c80, c60, c92, c61, c57, c70] c228 unsat228 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c227 := derived227 a h
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c229 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c93, some c128, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked229 : lratChecker f229 p229 = .success := by decide +kernel
theorem unsat229 : Unsatisfiable (PosFin 31) f229 := by
  apply lratCheckerSound f229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p229
  · intro a ha; simp [p229] at ha; subst a; trivial
  · exact checked229
theorem derived229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c229 := by
  apply localUnsat_implies_entails f229 [c5, c93, c128] c229 unsat229 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c230 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c60, some c89, some c1, some c130, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked230 : lratChecker f230 p230 = .success := by decide +kernel
theorem unsat230 : Unsatisfiable (PosFin 31) f230 := by
  apply lratCheckerSound f230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p230
  · intro a ha; simp [p230] at ha; subst a; trivial
  · exact checked230
theorem derived230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c230 := by
  apply localUnsat_implies_entails f230 [c229, c60, c89, c1, c130] c230 unsat230 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c231 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c65, some c130, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked231 : lratChecker f231 p231 = .success := by decide +kernel
theorem unsat231 : Unsatisfiable (PosFin 31) f231 := by
  apply lratCheckerSound f231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p231
  · intro a ha; simp [p231] at ha; subst a; trivial
  · exact checked231
theorem derived231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c231 := by
  apply localUnsat_implies_entails f231 [c65, c130] c231 unsat231 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c232 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c92, some c131, some c127, some c20, some c70, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked232 : lratChecker f232 p232 = .success := by decide +kernel
theorem unsat232 : Unsatisfiable (PosFin 31) f232 := by
  apply lratCheckerSound f232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p232
  · intro a ha; simp [p232] at ha; subst a; trivial
  · exact checked232
theorem derived232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c232 := by
  apply localUnsat_implies_entails f232 [c53, c92, c131, c127, c20, c70] c232 unsat232 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c233 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c231, some c5, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked233 : lratChecker f233 p233 = .success := by decide +kernel
theorem unsat233 : Unsatisfiable (PosFin 31) f233 := by
  apply lratCheckerSound f233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p233
  · intro a ha; simp [p233] at ha; subst a; trivial
  · exact checked233
theorem derived233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c233 := by
  apply localUnsat_implies_entails f233 [c33, c231, c5] c233 unsat233 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c231 := derived231 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c234 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c228, some c233, some c226, some c205, some c138, some c74, some c232, some c60, some c5, some c93, some c94, some c112, some c43, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked234 : lratChecker f234 p234 = .success := by decide +kernel
theorem unsat234 : Unsatisfiable (PosFin 31) f234 := by
  apply lratCheckerSound f234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p234
  · intro a ha; simp [p234] at ha; subst a; trivial
  · exact checked234
theorem derived234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c234 := by
  apply localUnsat_implies_entails f234 [c228, c233, c226, c205, c138, c74, c232, c60, c5, c93, c94, c112, c43] c234 unsat234 (by rfl) a
  have h0 : Entails.eval a c228 := derived228 a h
  have h1 : Entails.eval a c233 := derived233 a h
  have h2 : Entails.eval a c226 := derived226 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c232 := derived232 a h
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c235 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c230, some c138, some c5, some c93, some c94, some c112, some c111, some c43, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked235 : lratChecker f235 p235 = .success := by decide +kernel
theorem unsat235 : Unsatisfiable (PosFin 31) f235 := by
  apply lratCheckerSound f235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p235
  · intro a ha; simp [p235] at ha; subst a; trivial
  · exact checked235
theorem derived235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c235 := by
  apply localUnsat_implies_entails f235 [c230, c138, c5, c93, c94, c112, c111, c43] c235 unsat235 (by rfl) a
  have h0 : Entails.eval a c230 := derived230 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c236 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c228, some c226, some c205, some c233, some c234, some c235, some c38, some c42, some c99, some c131, some c20, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked236 : lratChecker f236 p236 = .success := by decide +kernel
theorem unsat236 : Unsatisfiable (PosFin 31) f236 := by
  apply lratCheckerSound f236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p236
  · intro a ha; simp [p236] at ha; subst a; trivial
  · exact checked236
theorem derived236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c236 := by
  apply localUnsat_implies_entails f236 [c228, c226, c205, c233, c234, c235, c38, c42, c99, c131, c20] c236 unsat236 (by rfl) a
  have h0 : Entails.eval a c228 := derived228 a h
  have h1 : Entails.eval a c226 := derived226 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c233 := derived233 a h
  have h4 : Entails.eval a c234 := derived234 a h
  have h5 : Entails.eval a c235 := derived235 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c237 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c4, some c38, some c78, some c125, some c154, some c182, some c49, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked237 : lratChecker f237 p237 = .success := by decide +kernel
theorem unsat237 : Unsatisfiable (PosFin 31) f237 := by
  apply lratCheckerSound f237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p237
  · intro a ha; simp [p237] at ha; subst a; trivial
  · exact checked237
theorem derived237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c237 := by
  apply localUnsat_implies_entails f237 [c4, c38, c78, c125, c154, c182, c49] c237 unsat237 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c238 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c228, some c236, some c4, some c107, some c103, some c237, some c5, some c94, some c220, some c66, some c125, some c53, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked238 : lratChecker f238 p238 = .success := by decide +kernel
theorem unsat238 : Unsatisfiable (PosFin 31) f238 := by
  apply lratCheckerSound f238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p238
  · intro a ha; simp [p238] at ha; subst a; trivial
  · exact checked238
theorem derived238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c238 := by
  apply localUnsat_implies_entails f238 [c226, c205, c228, c236, c4, c107, c103, c237, c5, c94, c220, c66, c125, c53] c238 unsat238 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c228 := derived228 a h
  have h3 : Entails.eval a c236 := derived236 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c237 := derived237 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c220 := derived220 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c239 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c226, some c205, some c5, some c93, some c94, some c118, some c120, some c8, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked239 : lratChecker f239 p239 = .success := by decide +kernel
theorem unsat239 : Unsatisfiable (PosFin 31) f239 := by
  apply lratCheckerSound f239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p239
  · intro a ha; simp [p239] at ha; subst a; trivial
  · exact checked239
theorem derived239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c239 := by
  apply localUnsat_implies_entails f239 [c238, c226, c205, c5, c93, c94, c118, c120, c8] c239 unsat239 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c226 := derived226 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c240 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c12, some c8, some c48, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked240 : lratChecker f240 p240 = .success := by decide +kernel
theorem unsat240 : Unsatisfiable (PosFin 31) f240 := by
  apply lratCheckerSound f240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p240
  · intro a ha; simp [p240] at ha; subst a; trivial
  · exact checked240
theorem derived240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c240 := by
  apply localUnsat_implies_entails f240 [c12, c8, c48] c240 unsat240 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c241 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c238, some c239, some c82, some c85, some c240, some c103, some c155, some c183, some c176, some c11, some c150, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked241 : lratChecker f241 p241 = .success := by decide +kernel
theorem unsat241 : Unsatisfiable (PosFin 31) f241 := by
  apply lratCheckerSound f241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p241
  · intro a ha; simp [p241] at ha; subst a; trivial
  · exact checked241
theorem derived241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c241 := by
  apply localUnsat_implies_entails f241 [c226, c205, c238, c239, c82, c85, c240, c103, c155, c183, c176, c11, c150] c241 unsat241 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c238 := derived238 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c240 := derived240 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c242 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c145, some c154, some c176, some c52, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked242 : lratChecker f242 p242 = .success := by decide +kernel
theorem unsat242 : Unsatisfiable (PosFin 31) f242 := by
  apply lratCheckerSound f242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p242
  · intro a ha; simp [p242] at ha; subst a; trivial
  · exact checked242
theorem derived242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c242 := by
  apply localUnsat_implies_entails f242 [c145, c154, c176, c52] c242 unsat242 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c243 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c238, some c239, some c82, some c85, some c240, some c49, some c162, some c133, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked243 : lratChecker f243 p243 = .success := by decide +kernel
theorem unsat243 : Unsatisfiable (PosFin 31) f243 := by
  apply lratCheckerSound f243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p243
  · intro a ha; simp [p243] at ha; subst a; trivial
  · exact checked243
theorem derived243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c243 := by
  apply localUnsat_implies_entails f243 [c226, c205, c238, c239, c82, c85, c240, c49, c162, c133] c243 unsat243 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c238 := derived238 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c240 := derived240 a h
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c244 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c238, some c239, some c82, some c85, some c240, some c127, some c103, some c241, some c243, some c30, some c242, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked244 : lratChecker f244 p244 = .success := by decide +kernel
theorem unsat244 : Unsatisfiable (PosFin 31) f244 := by
  apply lratCheckerSound f244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p244
  · intro a ha; simp [p244] at ha; subst a; trivial
  · exact checked244
theorem derived244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c244 := by
  apply localUnsat_implies_entails f244 [c226, c205, c238, c239, c82, c85, c240, c127, c103, c241, c243, c30, c242] c244 unsat244 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c238 := derived238 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c240 := derived240 a h
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c241 := derived241 a h
  have h10 : Entails.eval a c243 := derived243 a h
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c242 := derived242 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c245 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c205, some c238, some c239, some c82, some c85, some c240, some c127, some c103, some c244, some c48, some c90, some c123, some c159, some c158, some c22, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked245 : lratChecker f245 p245 = .success := by decide +kernel
theorem unsat245 : Unsatisfiable (PosFin 31) f245 := by
  apply lratCheckerSound f245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p245
  · intro a ha; simp [p245] at ha; subst a; trivial
  · exact checked245
theorem derived245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c245 := by
  apply localUnsat_implies_entails f245 [c226, c205, c238, c239, c82, c85, c240, c127, c103, c244, c48, c90, c123, c159, c158, c22] c245 unsat245 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c238 := derived238 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c240 := derived240 a h
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c244 := derived244 a h
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c246 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c226, some c205, some c239, some c82, some c245, some c230, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked246 : lratChecker f246 p246 = .success := by decide +kernel
theorem unsat246 : Unsatisfiable (PosFin 31) f246 := by
  apply lratCheckerSound f246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p246
  · intro a ha; simp [p246] at ha; subst a; trivial
  · exact checked246
theorem derived246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c246 := by
  apply localUnsat_implies_entails f246 [c238, c226, c205, c239, c82, c245, c230] c246 unsat246 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c226 := derived226 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c245 := derived245 a h
  have h6 : Entails.eval a c230 := derived230 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c247 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c246, some c19, some c226, some c205, some c56, some c57, some c165, some c188, some c157, some c50, some c43, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked247 : lratChecker f247 p247 = .success := by decide +kernel
theorem unsat247 : Unsatisfiable (PosFin 31) f247 := by
  apply lratCheckerSound f247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p247
  · intro a ha; simp [p247] at ha; subst a; trivial
  · exact checked247
theorem derived247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c247 := by
  apply localUnsat_implies_entails f247 [c238, c246, c19, c226, c205, c56, c57, c165, c188, c157, c50, c43] c247 unsat247 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c246 := derived246 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c226 := derived226 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c248 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c246, some c238, some c140, some c105, some c3, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked248 : lratChecker f248 p248 = .success := by decide +kernel
theorem unsat248 : Unsatisfiable (PosFin 31) f248 := by
  apply lratCheckerSound f248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p248
  · intro a ha; simp [p248] at ha; subst a; trivial
  · exact checked248
theorem derived248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c248 := by
  apply localUnsat_implies_entails f248 [c246, c238, c140, c105, c3] c248 unsat248 (by rfl) a
  have h0 : Entails.eval a c246 := derived246 a h
  have h1 : Entails.eval a c238 := derived238 a h
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c249 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c246, some c19, some c139, some c104, some c1, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked249 : lratChecker f249 p249 = .success := by decide +kernel
theorem unsat249 : Unsatisfiable (PosFin 31) f249 := by
  apply lratCheckerSound f249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p249
  · intro a ha; simp [p249] at ha; subst a; trivial
  · exact checked249
theorem derived249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c249 := by
  apply localUnsat_implies_entails f249 [c238, c246, c19, c139, c104, c1] c249 unsat249 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c246 := derived246 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c250 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c249, some c238, some c246, some c19, some c248, some c8, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked250 : lratChecker f250 p250 = .success := by decide +kernel
theorem unsat250 : Unsatisfiable (PosFin 31) f250 := by
  apply lratCheckerSound f250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p250
  · intro a ha; simp [p250] at ha; subst a; trivial
  · exact checked250
theorem derived250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c250 := by
  apply localUnsat_implies_entails f250 [c249, c238, c246, c19, c248, c8] c250 unsat250 (by rfl) a
  have h0 : Entails.eval a c249 := derived249 a h
  have h1 : Entails.eval a c238 := derived238 a h
  have h2 : Entails.eval a c246 := derived246 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c248 := derived248 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c251 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c85, some c120, some c247, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked251 : lratChecker f251 p251 = .success := by decide +kernel
theorem unsat251 : Unsatisfiable (PosFin 31) f251 := by
  apply lratCheckerSound f251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p251
  · intro a ha; simp [p251] at ha; subst a; trivial
  · exact checked251
theorem derived251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c251 := by
  apply localUnsat_implies_entails f251 [c85, c120, c247] c251 unsat251 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c247 := derived247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c252 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c250, some c251, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked252 : lratChecker f252 p252 = .success := by decide +kernel
theorem unsat252 : Unsatisfiable (PosFin 31) f252 := by
  apply lratCheckerSound f252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p252
  · intro a ha; simp [p252] at ha; subst a; trivial
  · exact checked252
theorem derived252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c252 := by
  apply localUnsat_implies_entails f252 [c238, c250, c251] c252 unsat252 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c250 := derived250 a h
  have h2 : Entails.eval a c251 := derived251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c253 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c152, some c181, some c157, some c50, some c43, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked253 : lratChecker f253 p253 = .success := by decide +kernel
theorem unsat253 : Unsatisfiable (PosFin 31) f253 := by
  apply lratCheckerSound f253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p253
  · intro a ha; simp [p253] at ha; subst a; trivial
  · exact checked253
theorem derived253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c253 := by
  apply localUnsat_implies_entails f253 [c252, c152, c181, c157, c50, c43] c253 unsat253 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c254 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c57, some c140, some c205, some c114, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked254 : lratChecker f254 p254 = .success := by decide +kernel
theorem unsat254 : Unsatisfiable (PosFin 31) f254 := by
  apply lratCheckerSound f254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p254
  · intro a ha; simp [p254] at ha; subst a; trivial
  · exact checked254
theorem derived254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c254 := by
  apply localUnsat_implies_entails f254 [c5, c57, c140, c205, c114] c254 unsat254 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c255 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c19, some c254, some c253, some c139, some c104, some c1, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked255 : lratChecker f255 p255 = .success := by decide +kernel
theorem unsat255 : Unsatisfiable (PosFin 31) f255 := by
  apply lratCheckerSound f255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p255
  · intro a ha; simp [p255] at ha; subst a; trivial
  · exact checked255
theorem derived255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c255 := by
  apply localUnsat_implies_entails f255 [c5, c19, c254, c253, c139, c104, c1] c255 unsat255 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c253 := derived253 a h
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c256 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c79, some c104, some c205, some c126, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked256 : lratChecker f256 p256 = .success := by decide +kernel
theorem unsat256 : Unsatisfiable (PosFin 31) f256 := by
  apply lratCheckerSound f256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p256
  · intro a ha; simp [p256] at ha; subst a; trivial
  · exact checked256
theorem derived256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c256 := by
  apply localUnsat_implies_entails f256 [c255, c79, c104, c205, c126] c256 unsat256 (by rfl) a
  have h0 : Entails.eval a c255 := derived255 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c257 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c256, some c1, some c139, some c126, some c205, some c16, some c109, some c151, some c168, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked257 : lratChecker f257 p257 = .success := by decide +kernel
theorem unsat257 : Unsatisfiable (PosFin 31) f257 := by
  apply lratCheckerSound f257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p257
  · intro a ha; simp [p257] at ha; subst a; trivial
  · exact checked257
theorem derived257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c257 := by
  apply localUnsat_implies_entails f257 [c252, c256, c1, c139, c126, c205, c16, c109, c151, c168] c257 unsat257 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c256 := derived256 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c258 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c255, some c257, some c95, some c102, some c16, some c114, some c46, some c156, some c184, some c185, some c140, some c50, some c149, some c201, some c204, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked258 : lratChecker f258 p258 = .success := by decide +kernel
theorem unsat258 : Unsatisfiable (PosFin 31) f258 := by
  apply lratCheckerSound f258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p258
  · intro a ha; simp [p258] at ha; subst a; trivial
  · exact checked258
theorem derived258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c258 := by
  apply localUnsat_implies_entails f258 [c252, c255, c257, c95, c102, c16, c114, c46, c156, c184, c185, c140, c50, c149, c201, c204] c258 unsat258 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c257 := derived257 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c259 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c127, some c230, some c55, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked259 : lratChecker f259 p259 = .success := by decide +kernel
theorem unsat259 : Unsatisfiable (PosFin 31) f259 := by
  apply lratCheckerSound f259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p259
  · intro a ha; simp [p259] at ha; subst a; trivial
  · exact checked259
theorem derived259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c259 := by
  apply localUnsat_implies_entails f259 [c127, c230, c55] c259 unsat259 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c230 := derived230 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c260 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c46, some c152, some c55, some c170, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked260 : lratChecker f260 p260 = .success := by decide +kernel
theorem unsat260 : Unsatisfiable (PosFin 31) f260 := by
  apply lratCheckerSound f260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p260
  · intro a ha; simp [p260] at ha; subst a; trivial
  · exact checked260
theorem derived260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c260 := by
  apply localUnsat_implies_entails f260 [c252, c46, c152, c55, c170] c260 unsat260 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c261 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c257, some c95, some c102, some c258, some c205, some c259, some c260, some c140, some c105, some c173, some c199, some c88, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked261 : lratChecker f261 p261 = .success := by decide +kernel
theorem unsat261 : Unsatisfiable (PosFin 31) f261 := by
  apply lratCheckerSound f261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p261
  · intro a ha; simp [p261] at ha; subst a; trivial
  · exact checked261
theorem derived261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c261 := by
  apply localUnsat_implies_entails f261 [c255, c257, c95, c102, c258, c205, c259, c260, c140, c105, c173, c199, c88] c261 unsat261 (by rfl) a
  have h0 : Entails.eval a c255 := derived255 a h
  have h1 : Entails.eval a c257 := derived257 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c258 := derived258 a h
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c259 := derived259 a h
  have h7 : Entails.eval a c260 := derived260 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c262 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c102, some c257, some c95, some c261, some c79, some c205, some c60, some c259, some c55, some c140, some c105, some c173, some c199, some c86, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked262 : lratChecker f262 p262 = .success := by decide +kernel
theorem unsat262 : Unsatisfiable (PosFin 31) f262 := by
  apply lratCheckerSound f262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p262
  · intro a ha; simp [p262] at ha; subst a; trivial
  · exact checked262
theorem derived262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c262 := by
  apply localUnsat_implies_entails f262 [c255, c102, c257, c95, c261, c79, c205, c60, c259, c55, c140, c105, c173, c199, c86] c262 unsat262 (by rfl) a
  have h0 : Entails.eval a c255 := derived255 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c257 := derived257 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c261 := derived261 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c259 := derived259 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c263 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c46, some c152, some c181, some c52, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked263 : lratChecker f263 p263 = .success := by decide +kernel
theorem unsat263 : Unsatisfiable (PosFin 31) f263 := by
  apply lratCheckerSound f263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p263
  · intro a ha; simp [p263] at ha; subst a; trivial
  · exact checked263
theorem derived263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c263 := by
  apply localUnsat_implies_entails f263 [c252, c46, c152, c181, c52] c263 unsat263 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c264 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c19, some c127, some c205, some c13, some c16, some c168, some c191, some c49, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked264 : lratChecker f264 p264 = .success := by decide +kernel
theorem unsat264 : Unsatisfiable (PosFin 31) f264 := by
  apply lratCheckerSound f264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p264
  · intro a ha; simp [p264] at ha; subst a; trivial
  · exact checked264
theorem derived264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c264 := by
  apply localUnsat_implies_entails f264 [c262, c19, c127, c205, c13, c16, c168, c191, c49] c264 unsat264 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c265 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c255, some c102, some c262, some c19, some c264, some c46, some c263, some c16, some c126, some c205, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked265 : lratChecker f265 p265 = .success := by decide +kernel
theorem unsat265 : Unsatisfiable (PosFin 31) f265 := by
  apply lratCheckerSound f265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p265
  · intro a ha; simp [p265] at ha; subst a; trivial
  · exact checked265
theorem derived265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c265 := by
  apply localUnsat_implies_entails f265 [c252, c255, c102, c262, c19, c264, c46, c263, c16, c126, c205] c265 unsat265 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c262 := derived262 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c264 := derived264 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c263 := derived263 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c266 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c265, some c137, some c205, some c16, some c151, some c144, some c154, some c208, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked266 : lratChecker f266 p266 = .success := by decide +kernel
theorem unsat266 : Unsatisfiable (PosFin 31) f266 := by
  apply lratCheckerSound f266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p266
  · intro a ha; simp [p266] at ha; subst a; trivial
  · exact checked266
theorem derived266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c266 := by
  apply localUnsat_implies_entails f266 [c252, c265, c137, c205, c16, c151, c144, c154, c208] c266 unsat266 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c265 := derived265 a h
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c267 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c151, some c46, some c45, some c154, some c169, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked267 : lratChecker f267 p267 = .success := by decide +kernel
theorem unsat267 : Unsatisfiable (PosFin 31) f267 := by
  apply lratCheckerSound f267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p267
  · intro a ha; simp [p267] at ha; subst a; trivial
  · exact checked267
theorem derived267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c267 := by
  apply localUnsat_implies_entails f267 [c252, c151, c46, c45, c154, c169] c267 unsat267 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c268 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c265, some c137, some c266, some c267, some c16, some c166, some c143, some c206, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked268 : lratChecker f268 p268 = .success := by decide +kernel
theorem unsat268 : Unsatisfiable (PosFin 31) f268 := by
  apply lratCheckerSound f268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p268
  · intro a ha; simp [p268] at ha; subst a; trivial
  · exact checked268
theorem derived268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c268 := by
  apply localUnsat_implies_entails f268 [c265, c137, c266, c267, c16, c166, c143, c206] c268 unsat268 (by rfl) a
  have h0 : Entails.eval a c265 := derived265 a h
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c267 := derived267 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c269 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c143, some c45, some c49, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked269 : lratChecker f269 p269 = .success := by decide +kernel
theorem unsat269 : Unsatisfiable (PosFin 31) f269 := by
  apply lratCheckerSound f269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p269
  · intro a ha; simp [p269] at ha; subst a; trivial
  · exact checked269
theorem derived269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c269 := by
  apply localUnsat_implies_entails f269 [c252, c143, c45, c49] c269 unsat269 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c270 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c265, some c137, some c268, some c263, some c16, some c269, some c52, some c145, some c44, some c49, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked270 : lratChecker f270 p270 = .success := by decide +kernel
theorem unsat270 : Unsatisfiable (PosFin 31) f270 := by
  apply lratCheckerSound f270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p270
  · intro a ha; simp [p270] at ha; subst a; trivial
  · exact checked270
theorem derived270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c270 := by
  apply localUnsat_implies_entails f270 [c252, c265, c137, c268, c263, c16, c269, c52, c145, c44, c49] c270 unsat270 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c265 := derived265 a h
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c268 := derived268 a h
  have h4 : Entails.eval a c263 := derived263 a h
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c269 := derived269 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c271 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c154, some c182, some c49, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked271 : lratChecker f271 p271 = .success := by decide +kernel
theorem unsat271 : Unsatisfiable (PosFin 31) f271 := by
  apply lratCheckerSound f271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p271
  · intro a ha; simp [p271] at ha; subst a; trivial
  · exact checked271
theorem derived271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c271 := by
  apply localUnsat_implies_entails f271 [c154, c182, c49] c271 unsat271 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c182 := h 181 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c272 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c169, some c192, some c45, some c44, some c49, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked272 : lratChecker f272 p272 = .success := by decide +kernel
theorem unsat272 : Unsatisfiable (PosFin 31) f272 := by
  apply lratCheckerSound f272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p272
  · intro a ha; simp [p272] at ha; subst a; trivial
  · exact checked272
theorem derived272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c272 := by
  apply localUnsat_implies_entails f272 [c252, c169, c192, c45, c44, c49] c272 unsat272 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c273 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c272, some c205, some c167, some c144, some c208, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked273 : lratChecker f273 p273 = .success := by decide +kernel
theorem unsat273 : Unsatisfiable (PosFin 31) f273 := by
  apply lratCheckerSound f273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p273
  · intro a ha; simp [p273] at ha; subst a; trivial
  · exact checked273
theorem derived273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c273 := by
  apply localUnsat_implies_entails f273 [c252, c272, c205, c167, c144, c208] c273 unsat273 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c272 := derived272 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c274 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c271, some c273, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked274 : lratChecker f274 p274 = .success := by decide +kernel
theorem unsat274 : Unsatisfiable (PosFin 31) f274 := by
  apply lratCheckerSound f274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p274
  · intro a ha; simp [p274] at ha; subst a; trivial
  · exact checked274
theorem derived274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c274 := by
  apply localUnsat_implies_entails f274 [c271, c273] c274 unsat274 (by rfl) a
  have h0 : Entails.eval a c271 := derived271 a h
  have h1 : Entails.eval a c273 := derived273 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c275 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c137, some c268, some c263, some c270, some c274, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked275 : lratChecker f275 p275 = .success := by decide +kernel
theorem unsat275 : Unsatisfiable (PosFin 31) f275 := by
  apply lratCheckerSound f275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p275
  · intro a ha; simp [p275] at ha; subst a; trivial
  · exact checked275
theorem derived275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c275 := by
  apply localUnsat_implies_entails f275 [c137, c268, c263, c270, c274] c275 unsat275 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c268 := derived268 a h
  have h2 : Entails.eval a c263 := derived263 a h
  have h3 : Entails.eval a c270 := derived270 a h
  have h4 : Entails.eval a c274 := derived274 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c276 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c265, some c275, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked276 : lratChecker f276 p276 = .success := by decide +kernel
theorem unsat276 : Unsatisfiable (PosFin 31) f276 := by
  apply lratCheckerSound f276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p276
  · intro a ha; simp [p276] at ha; subst a; trivial
  · exact checked276
theorem derived276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c276 := by
  apply localUnsat_implies_entails f276 [c265, c275] c276 unsat276 (by rfl) a
  have h0 : Entails.eval a c265 := derived265 a h
  have h1 : Entails.eval a c275 := derived275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c277 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c276, some c4, some c274, some c45, some c15, some c52, some c7, some c10, some c11, some c145, some c44, some c175, some c225, some c194, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked277 : lratChecker f277 p277 = .success := by decide +kernel
theorem unsat277 : Unsatisfiable (PosFin 31) f277 := by
  apply lratCheckerSound f277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p277
  · intro a ha; simp [p277] at ha; subst a; trivial
  · exact checked277
theorem derived277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c277 := by
  apply localUnsat_implies_entails f277 [c252, c276, c4, c274, c45, c15, c52, c7, c10, c11, c145, c44, c175, c225, c194] c277 unsat277 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c175 := h 174 (by decide)
  have h13 : Entails.eval a c225 := derived225 a h
  have h14 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c278 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c276, some c274, some c112, some c4, some c277, some c49, some c44, some c52, some c14, some c142, some c269, some c9, some c136, some c193, some c83, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked278 : lratChecker f278 p278 = .success := by decide +kernel
theorem unsat278 : Unsatisfiable (PosFin 31) f278 := by
  apply lratCheckerSound f278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p278
  · intro a ha; simp [p278] at ha; subst a; trivial
  · exact checked278
theorem derived278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c278 := by
  apply localUnsat_implies_entails f278 [c252, c276, c274, c112, c4, c277, c49, c44, c52, c14, c142, c269, c9, c136, c193, c83] c278 unsat278 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c274 := derived274 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c277 := derived277 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c269 := derived269 a h
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c279 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c276, some c278, some c125, some c46, some c112, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked279 : lratChecker f279 p279 = .success := by decide +kernel
theorem unsat279 : Unsatisfiable (PosFin 31) f279 := by
  apply lratCheckerSound f279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p279
  · intro a ha; simp [p279] at ha; subst a; trivial
  · exact checked279
theorem derived279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c279 := by
  apply localUnsat_implies_entails f279 [c252, c276, c278, c125, c46, c112] c279 unsat279 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c278 := derived278 a h
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c280 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c279, some c276, some c112, some c124, some c152, some c181, some c52, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked280 : lratChecker f280 p280 = .success := by decide +kernel
theorem unsat280 : Unsatisfiable (PosFin 31) f280 := by
  apply lratCheckerSound f280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p280
  · intro a ha; simp [p280] at ha; subst a; trivial
  · exact checked280
theorem derived280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c280 := by
  apply localUnsat_implies_entails f280 [c252, c279, c276, c112, c124, c152, c181, c52] c280 unsat280 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c279 := derived279 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c281 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c179, some c203, some c1, some c18, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked281 : lratChecker f281 p281 = .success := by decide +kernel
theorem unsat281 : Unsatisfiable (PosFin 31) f281 := by
  apply lratCheckerSound f281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p281
  · intro a ha; simp [p281] at ha; subst a; trivial
  · exact checked281
theorem derived281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c281 := by
  apply localUnsat_implies_entails f281 [c179, c203, c1, c18] c281 unsat281 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c282 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c279, some c276, some c280, some c75, some c108, some c62, some c33, some c281, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked282 : lratChecker f282 p282 = .success := by decide +kernel
theorem unsat282 : Unsatisfiable (PosFin 31) f282 := by
  apply lratCheckerSound f282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p282
  · intro a ha; simp [p282] at ha; subst a; trivial
  · exact checked282
theorem derived282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c282 := by
  apply localUnsat_implies_entails f282 [c252, c279, c276, c280, c75, c108, c62, c33, c281] c282 unsat282 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c279 := derived279 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c280 := derived280 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c281 := derived281 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c283 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c75, some c108, some c62, some c63, some c28, some c33, some c97, some c20, some c59, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked283 : lratChecker f283 p283 = .success := by decide +kernel
theorem unsat283 : Unsatisfiable (PosFin 31) f283 := by
  apply lratCheckerSound f283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p283
  · intro a ha; simp [p283] at ha; subst a; trivial
  · exact checked283
theorem derived283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c283 := by
  apply localUnsat_implies_entails f283 [c252, c75, c108, c62, c63, c28, c33, c97, c20, c59] c283 unsat283 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c284 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c279, some c282, some c283, some c112, some c4, some c78, some c62, some c63, some c97, some c66, some c53, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked284 : lratChecker f284 p284 = .success := by decide +kernel
theorem unsat284 : Unsatisfiable (PosFin 31) f284 := by
  apply lratCheckerSound f284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p284
  · intro a ha; simp [p284] at ha; subst a; trivial
  · exact checked284
theorem derived284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c284 := by
  apply localUnsat_implies_entails f284 [c276, c279, c282, c283, c112, c4, c78, c62, c63, c97, c66, c53] c284 unsat284 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c279 := derived279 a h
  have h2 : Entails.eval a c282 := derived282 a h
  have h3 : Entails.eval a c283 := derived283 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c285 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c276, some c110, some c225, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked285 : lratChecker f285 p285 = .success := by decide +kernel
theorem unsat285 : Unsatisfiable (PosFin 31) f285 := by
  apply lratCheckerSound f285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p285
  · intro a ha; simp [p285] at ha; subst a; trivial
  · exact checked285
theorem derived285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c285 := by
  apply localUnsat_implies_entails f285 [c284, c276, c110, c225] c285 unsat285 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c225 := derived225 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c286 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c276, some c1, some c285, some c205, some c53, some c57, some c127, some c273, some c237, some c135, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked286 : lratChecker f286 p286 = .success := by decide +kernel
theorem unsat286 : Unsatisfiable (PosFin 31) f286 := by
  apply lratCheckerSound f286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p286
  · intro a ha; simp [p286] at ha; subst a; trivial
  · exact checked286
theorem derived286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c286 := by
  apply localUnsat_implies_entails f286 [c284, c276, c1, c285, c205, c53, c57, c127, c273, c237, c135] c286 unsat286 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c285 := derived285 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c273 := derived273 a h
  have h9 : Entails.eval a c237 := derived237 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c287 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c276, some c57, some c60, some c78, some c4, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked287 : lratChecker f287 p287 = .success := by decide +kernel
theorem unsat287 : Unsatisfiable (PosFin 31) f287 := by
  apply lratCheckerSound f287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p287
  · intro a ha; simp [p287] at ha; subst a; trivial
  · exact checked287
theorem derived287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c287 := by
  apply localUnsat_implies_entails f287 [c284, c276, c57, c60, c78, c4] c287 unsat287 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c288 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c276, some c287, some c205, some c129, some c96, some c31, some c97, some c4, some c40, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked288 : lratChecker f288 p288 = .success := by decide +kernel
theorem unsat288 : Unsatisfiable (PosFin 31) f288 := by
  apply lratCheckerSound f288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p288
  · intro a ha; simp [p288] at ha; subst a; trivial
  · exact checked288
theorem derived288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c288 := by
  apply localUnsat_implies_entails f288 [c284, c276, c287, c205, c129, c96, c31, c97, c4, c40] c288 unsat288 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c289 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c288, some c284, some c276, some c205, some c129, some c110, some c225, some c171, some c197, some c49, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked289 : lratChecker f289 p289 = .success := by decide +kernel
theorem unsat289 : Unsatisfiable (PosFin 31) f289 := by
  apply lratCheckerSound f289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p289
  · intro a ha; simp [p289] at ha; subst a; trivial
  · exact checked289
theorem derived289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c289 := by
  apply localUnsat_implies_entails f289 [c288, c284, c276, c205, c129, c110, c225, c171, c197, c49] c289 unsat289 (by rfl) a
  have h0 : Entails.eval a c288 := derived288 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c225 := derived225 a h
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c290 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c284, some c276, some c288, some c286, some c289, some c57, some c127, some c78, some c4, some c65, some c135, some c170, some c196, some c45, some c44, some c49, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked290 : lratChecker f290 p290 = .success := by decide +kernel
theorem unsat290 : Unsatisfiable (PosFin 31) f290 := by
  apply lratCheckerSound f290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p290
  · intro a ha; simp [p290] at ha; subst a; trivial
  · exact checked290
theorem derived290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c290 := by
  apply localUnsat_implies_entails f290 [c252, c284, c276, c288, c286, c289, c57, c127, c78, c4, c65, c135, c170, c196, c45, c44, c49] c290 unsat290 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c288 := derived288 a h
  have h4 : Entails.eval a c286 := derived286 a h
  have h5 : Entails.eval a c289 := derived289 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c291 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c57, some c38, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked291 : lratChecker f291 p291 = .success := by decide +kernel
theorem unsat291 : Unsatisfiable (PosFin 31) f291 := by
  apply lratCheckerSound f291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p291
  · intro a ha; simp [p291] at ha; subst a; trivial
  · exact checked291
theorem derived291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c291 := by
  apply localUnsat_implies_entails f291 [c57, c38] c291 unsat291 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c292 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c284, some c290, some c274, some c276, some c75, some c291, some c205, some c108, some c129, some c68, some c5, some c225, some c184, some c156, some c148, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked292 : lratChecker f292 p292 = .success := by decide +kernel
theorem unsat292 : Unsatisfiable (PosFin 31) f292 := by
  apply lratCheckerSound f292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p292
  · intro a ha; simp [p292] at ha; subst a; trivial
  · exact checked292
theorem derived292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c292 := by
  apply localUnsat_implies_entails f292 [c252, c284, c290, c274, c276, c75, c291, c205, c108, c129, c68, c5, c225, c184, c156, c148] c292 unsat292 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c290 := derived290 a h
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c276 := derived276 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c291 := derived291 a h
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c225 := derived225 a h
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c156 := h 155 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c293 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c284, some c276, some c290, some c274, some c75, some c291, some c205, some c292, some c39, some c168, some c191, some c49, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked293 : lratChecker f293 p293 = .success := by decide +kernel
theorem unsat293 : Unsatisfiable (PosFin 31) f293 := by
  apply lratCheckerSound f293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p293
  · intro a ha; simp [p293] at ha; subst a; trivial
  · exact checked293
theorem derived293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c293 := by
  apply localUnsat_implies_entails f293 [c252, c284, c276, c290, c274, c75, c291, c205, c292, c39, c168, c191, c49] c293 unsat293 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c290 := derived290 a h
  have h4 : Entails.eval a c274 := derived274 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c291 := derived291 a h
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c292 := derived292 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c294 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c205, some c75, some c151, some c39, some c168, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked294 : lratChecker f294 p294 = .success := by decide +kernel
theorem unsat294 : Unsatisfiable (PosFin 31) f294 := by
  apply lratCheckerSound f294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p294
  · intro a ha; simp [p294] at ha; subst a; trivial
  · exact checked294
theorem derived294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c294 := by
  apply localUnsat_implies_entails f294 [c252, c205, c75, c151, c39, c168] c294 unsat294 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c151 := h 150 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c295 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c284, some c129, some c205, some c293, some c96, some c5, some c97, some c225, some c253, some c294, some c31, some c40, some c4, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked295 : lratChecker f295 p295 = .success := by decide +kernel
theorem unsat295 : Unsatisfiable (PosFin 31) f295 := by
  apply lratCheckerSound f295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p295
  · intro a ha; simp [p295] at ha; subst a; trivial
  · exact checked295
theorem derived295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c295 := by
  apply localUnsat_implies_entails f295 [c276, c284, c129, c205, c293, c96, c5, c97, c225, c253, c294, c31, c40, c4] c295 unsat295 (by rfl) a
  have h0 : Entails.eval a c276 := derived276 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c293 := derived293 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c225 := derived225 a h
  have h9 : Entails.eval a c253 := derived253 a h
  have h10 : Entails.eval a c294 := derived294 a h
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c296 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨23, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c295, some c276, some c284, some c129, some c205, some c293, some c285, some c31, some c171, some c4, some c164, some c78, some c253, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked296 : lratChecker f296 p296 = .success := by decide +kernel
theorem unsat296 : Unsatisfiable (PosFin 31) f296 := by
  apply lratCheckerSound f296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p296
  · intro a ha; simp [p296] at ha; subst a; trivial
  · exact checked296
theorem derived296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c296 := by
  apply localUnsat_implies_entails f296 [c295, c276, c284, c129, c205, c293, c285, c31, c171, c4, c164, c78, c253] c296 unsat296 (by rfl) a
  have h0 : Entails.eval a c295 := derived295 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c293 := derived293 a h
  have h6 : Entails.eval a c285 := derived285 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c253 := derived253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c297 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c293, some c276, some c205, some c295, some c296, some c108, some c281, some c29, some c43, some c168, some c151, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked297 : lratChecker f297 p297 = .success := by decide +kernel
theorem unsat297 : Unsatisfiable (PosFin 31) f297 := by
  apply lratCheckerSound f297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p297
  · intro a ha; simp [p297] at ha; subst a; trivial
  · exact checked297
theorem derived297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c297 := by
  apply localUnsat_implies_entails f297 [c252, c293, c276, c205, c295, c296, c108, c281, c29, c43, c168, c151] c297 unsat297 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c293 := derived293 a h
  have h2 : Entails.eval a c276 := derived276 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c295 := derived295 a h
  have h5 : Entails.eval a c296 := derived296 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c281 := derived281 a h
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c298 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c297, some c293, some c276, some c46, some c108, some c281, some c89, some c233, some c135, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked298 : lratChecker f298 p298 = .success := by decide +kernel
theorem unsat298 : Unsatisfiable (PosFin 31) f298 := by
  apply lratCheckerSound f298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p298
  · intro a ha; simp [p298] at ha; subst a; trivial
  · exact checked298
theorem derived298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c298 := by
  apply localUnsat_implies_entails f298 [c252, c297, c293, c276, c46, c108, c281, c89, c233, c135] c298 unsat298 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c297 := derived297 a h
  have h2 : Entails.eval a c293 := derived293 a h
  have h3 : Entails.eval a c276 := derived276 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c281 := derived281 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c233 := derived233 a h
  have h9 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c299 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c297, some c293, some c233, some c24, some c135, some c263, some c89, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 31) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c297, c293, c233, c24, c135, c263, c89] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c297 := derived297 a h
  have h1 : Entails.eval a c293 := derived293 a h
  have h2 : Entails.eval a c233 := derived233 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c263 := derived263 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c300 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c297, some c293, some c284, some c299, some c1, some c53, some c135, some c263, some c126, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 31) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c297, c293, c284, c299, c1, c53, c135, c263, c126] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c297 := derived297 a h
  have h1 : Entails.eval a c293 := derived293 a h
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c299 := derived299 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c263 := derived263 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c301 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c297, some c293, some c284, some c276, some c298, some c300, some c4, some c125, some c78, some c89, some c5, some c101, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked301 : lratChecker f301 p301 = .success := by decide +kernel
theorem unsat301 : Unsatisfiable (PosFin 31) f301 := by
  apply lratCheckerSound f301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p301
  · intro a ha; simp [p301] at ha; subst a; trivial
  · exact checked301
theorem derived301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c301 := by
  apply localUnsat_implies_entails f301 [c297, c293, c284, c276, c298, c300, c4, c125, c78, c89, c5, c101] c301 unsat301 (by rfl) a
  have h0 : Entails.eval a c297 := derived297 a h
  have h1 : Entails.eval a c293 := derived293 a h
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c276 := derived276 a h
  have h4 : Entails.eval a c298 := derived298 a h
  have h5 : Entails.eval a c300 := derived300 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c302 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c301, some c297, some c293, some c284, some c276, some c4, some c108, some c78, some c34, some c5, some c253, some c101, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked302 : lratChecker f302 p302 = .success := by decide +kernel
theorem unsat302 : Unsatisfiable (PosFin 31) f302 := by
  apply lratCheckerSound f302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p302
  · intro a ha; simp [p302] at ha; subst a; trivial
  · exact checked302
theorem derived302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c302 := by
  apply localUnsat_implies_entails f302 [c252, c301, c297, c293, c284, c276, c4, c108, c78, c34, c5, c253, c101] c302 unsat302 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c301 := derived301 a h
  have h2 : Entails.eval a c297 := derived297 a h
  have h3 : Entails.eval a c293 := derived293 a h
  have h4 : Entails.eval a c284 := derived284 a h
  have h5 : Entails.eval a c276 := derived276 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c253 := derived253 a h
  have h12 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c303 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c293, some c297, some c301, some c302, some c60, some c5, some c56, some c253, some c135, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked303 : lratChecker f303 p303 = .success := by decide +kernel
theorem unsat303 : Unsatisfiable (PosFin 31) f303 := by
  apply lratCheckerSound f303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p303
  · intro a ha; simp [p303] at ha; subst a; trivial
  · exact checked303
theorem derived303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c303 := by
  apply localUnsat_implies_entails f303 [c284, c293, c297, c301, c302, c60, c5, c56, c253, c135] c303 unsat303 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c293 := derived293 a h
  have h2 : Entails.eval a c297 := derived297 a h
  have h3 : Entails.eval a c301 := derived301 a h
  have h4 : Entails.eval a c302 := derived302 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c253 := derived253 a h
  have h9 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c304 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c101, some c19, some c4, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked304 : lratChecker f304 p304 = .success := by decide +kernel
theorem unsat304 : Unsatisfiable (PosFin 31) f304 := by
  apply lratCheckerSound f304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p304
  · intro a ha; simp [p304] at ha; subst a; trivial
  · exact checked304
theorem derived304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c304 := by
  apply localUnsat_implies_entails f304 [c101, c19, c4] c304 unsat304 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c305 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c48, some c152, some c181, some c146, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked305 : lratChecker f305 p305 = .success := by decide +kernel
theorem unsat305 : Unsatisfiable (PosFin 31) f305 := by
  apply lratCheckerSound f305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p305
  · intro a ha; simp [p305] at ha; subst a; trivial
  · exact checked305
theorem derived305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c305 := by
  apply localUnsat_implies_entails f305 [c252, c48, c152, c181, c146] c305 unsat305 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c306 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c305, some c46, some c263, some c166, some c189, some c45, some c44, some c47, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked306 : lratChecker f306 p306 = .success := by decide +kernel
theorem unsat306 : Unsatisfiable (PosFin 31) f306 := by
  apply lratCheckerSound f306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p306
  · intro a ha; simp [p306] at ha; subst a; trivial
  · exact checked306
theorem derived306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c306 := by
  apply localUnsat_implies_entails f306 [c252, c305, c46, c263, c166, c189, c45, c44, c47] c306 unsat306 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c305 := derived305 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c263 := derived263 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c307 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c306, some c48, some c274, some c166, some c45, some c269, some c164, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked307 : lratChecker f307 p307 = .success := by decide +kernel
theorem unsat307 : Unsatisfiable (PosFin 31) f307 := by
  apply lratCheckerSound f307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p307
  · intro a ha; simp [p307] at ha; subst a; trivial
  · exact checked307
theorem derived307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c307 := by
  apply localUnsat_implies_entails f307 [c252, c306, c48, c274, c166, c45, c269, c164] c307 unsat307 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c306 := derived306 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c269 := derived269 a h
  have h7 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c308 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c45, some c49, some c44, some c269, some c274, some c307, some c304, some c116, some c133, some c200, some c210, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked308 : lratChecker f308 p308 = .success := by decide +kernel
theorem unsat308 : Unsatisfiable (PosFin 31) f308 := by
  apply lratCheckerSound f308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p308
  · intro a ha; simp [p308] at ha; subst a; trivial
  · exact checked308
theorem derived308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c308 := by
  apply localUnsat_implies_entails f308 [c252, c303, c306, c45, c49, c44, c269, c274, c307, c304, c116, c133, c200, c210] c308 unsat308 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c269 := derived269 a h
  have h7 : Entails.eval a c274 := derived274 a h
  have h8 : Entails.eval a c307 := derived307 a h
  have h9 : Entails.eval a c304 := derived304 a h
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c309 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c45, some c49, some c269, some c308, some c27, some c135, some c178, some c6, some c3, some c100, some c161, some c64, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked309 : lratChecker f309 p309 = .success := by decide +kernel
theorem unsat309 : Unsatisfiable (PosFin 31) f309 := by
  apply lratCheckerSound f309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p309
  · intro a ha; simp [p309] at ha; subst a; trivial
  · exact checked309
theorem derived309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c309 := by
  apply localUnsat_implies_entails f309 [c252, c303, c306, c45, c49, c269, c308, c27, c135, c178, c6, c3, c100, c161, c64] c309 unsat309 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c269 := derived269 a h
  have h6 : Entails.eval a c308 := derived308 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c310 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f310 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c274, some c45, some c269, some c49, some c44, some c309, some c127, some c94, some c103, some c138, some c4, some c79, some c113, some c186, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p310 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked310 : lratChecker f310 p310 = .success := by decide +kernel
theorem unsat310 : Unsatisfiable (PosFin 31) f310 := by
  apply lratCheckerSound f310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p310
  · intro a ha; simp [p310] at ha; subst a; trivial
  · exact checked310
theorem derived310 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c310 := by
  apply localUnsat_implies_entails f310 [c252, c303, c306, c274, c45, c269, c49, c44, c309, c127, c94, c103, c138, c4, c79, c113, c186] c310 unsat310 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c269 := derived269 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c309 := derived309 a h
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived310

end CochromaticTwenty.Certificates.Z12Direct_5_3_4
