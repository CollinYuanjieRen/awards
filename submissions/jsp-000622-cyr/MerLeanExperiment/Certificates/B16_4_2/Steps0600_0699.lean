import MerLeanExperiment.Certificates.B16_4_2.Steps0500_0599

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c984 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c213, some c268, some c525, some c20, some c116, some c983, some c773, some c317, some c34, some c982, some c13, some c138, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 57) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c18, c213, c268, c525, c20, c116, c983, c773, c317, c34, c982, c13, c138] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c213 := h 212 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c773 := derived773 a h
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c982 := derived982 a h
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c984, some c69, some c40, some c144, some c983, some c773, some c318, some c134, some c63, some c155, some c205, some c16, some c165, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 57) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c984, c69, c40, c144, c983, c773, c318, c134, c63, c155, c205, c16, c165] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c984 := derived984 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c773 := derived773 a h
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c985, some c317, some c214, some c62, some c154, some c20, some c116, some c13, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 57) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c18, c985, c317, c214, c62, c154, c20, c116, c13] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c985 := derived985 a h
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c987 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨44, by decide⟩, true), (⟨12, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨53, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c165, some c176, some c198, some c196, some c367, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 57) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c165, c176, c198, c196, c367] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c165 := h 164 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c973, some c18, some c980, some c979, some c359, some c360, some c69, some c112, some c49, some c984, some c123, some c330, some c87, some c986, some c316, some c289, some c40, some c144, some c280, some c85, some c987, some c205, some c134, some c215, some c270, some c269, some c146, some c233, some c232, some c354, some c275, some c227, some c211, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 57) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c930, c973, c18, c980, c979, c359, c360, c69, c112, c49, c984, c123, c330, c87, c986, c316, c289, c40, c144, c280, c85, c987, c205, c134, c215, c270, c269, c146, c233, c232, c354, c275, c227, c211] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c973 := derived973 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c980 := derived980 a h
  have h4 : Entails.eval a c979 := derived979 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c984 := derived984 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c986 := derived986 a h
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c40 := h 39 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c85 := h 84 (by decide)
  have h21 : Entails.eval a c987 := derived987 a h
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c134 := h 133 (by decide)
  have h24 : Entails.eval a c215 := h 214 (by decide)
  have h25 : Entails.eval a c270 := h 269 (by decide)
  have h26 : Entails.eval a c269 := h 268 (by decide)
  have h27 : Entails.eval a c146 := h 145 (by decide)
  have h28 : Entails.eval a c233 := h 232 (by decide)
  have h29 : Entails.eval a c232 := h 231 (by decide)
  have h30 : Entails.eval a c354 := h 353 (by decide)
  have h31 : Entails.eval a c275 := h 274 (by decide)
  have h32 : Entails.eval a c227 := h 226 (by decide)
  have h33 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c280, some c867, some c360, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c40, c280, c867, c360] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c867 := derived867 a h
  have h3 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c988, some c930, some c973, some c18, some c980, some c316, some c320, some c989, some c359, some c867, some c68, some c60, some c112, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 57) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c988, c930, c973, c18, c980, c316, c320, c989, c359, c867, c68, c60, c112] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c988 := derived988 a h
  have h1 : Entails.eval a c930 := derived930 a h
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c980 := derived980 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c989 := derived989 a h
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c867 := derived867 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c990, some c988, some c930, some c973, some c18, some c980, some c359, some c867, some c68, some c48, some c112, some c60, some c313, some c944, some c945, some c318, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 57) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c990, c988, c930, c973, c18, c980, c359, c867, c68, c48, c112, c60, c313, c944, c945, c318] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c990 := derived990 a h
  have h1 : Entails.eval a c988 := derived988 a h
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c973 := derived973 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c980 := derived980 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c867 := derived867 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c944 := derived944 a h
  have h14 : Entails.eval a c945 := derived945 a h
  have h15 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c318, some c155, some c281, some c202, some c354, some c118, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 57) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c773, c318, c155, c281, c202, c354, c118] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c990, some c988, some c930, some c973, some c18, some c980, some c991, some c40, some c144, some c989, some c313, some c150, some c275, some c992, some c154, some c13, some c50, some c197, some c186, some c303, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 57) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c990, c988, c930, c973, c18, c980, c991, c40, c144, c989, c313, c150, c275, c992, c154, c13, c50, c197, c186, c303] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c990 := derived990 a h
  have h1 : Entails.eval a c988 := derived988 a h
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c973 := derived973 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c980 := derived980 a h
  have h6 : Entails.eval a c991 := derived991 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c989 := derived989 a h
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c992 := derived992 a h
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨14, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c202, some c3, some c155, some c65, some c216, some c354, some c233, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c18, c202, c3, c155, c65, c216, c354, c233] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c990, some c930, some c993, some c317, some c154, some c973, some c18, some c214, some c980, some c20, some c116, some c867, some c13, some c205, some c360, some c42, some c165, some c69, some c232, some c994, some c631, some c161, some c267, some c354, some c233, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c990, c930, c993, c317, c154, c973, c18, c214, c980, c20, c116, c867, c13, c205, c360, c42, c165, c69, c232, c994, c631, c161, c267, c354, c233] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c990 := derived990 a h
  have h1 : Entails.eval a c930 := derived930 a h
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c973 := derived973 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  have h8 : Entails.eval a c980 := derived980 a h
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c867 := derived867 a h
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c994 := derived994 a h
  have h20 : Entails.eval a c631 := derived631 a h
  have h21 : Entails.eval a c161 := h 160 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  have h23 : Entails.eval a c354 := h 353 (by decide)
  have h24 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c977, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c117, c977] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c977 := derived977 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c997 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c973, some c18, some c980, some c988, some c990, some c993, some c317, some c214, some c154, some c995, some c359, some c867, some c68, some c112, some c32, some c996, some c222, some c265, some c64, some c631, some c27, some c2, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 57) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c930, c973, c18, c980, c988, c990, c993, c317, c214, c154, c995, c359, c867, c68, c112, c32, c996, c222, c265, c64, c631, c27, c2] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c973 := derived973 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c980 := derived980 a h
  have h4 : Entails.eval a c988 := derived988 a h
  have h5 : Entails.eval a c990 := derived990 a h
  have h6 : Entails.eval a c993 := derived993 a h
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c214 := h 213 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c995 := derived995 a h
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c867 := derived867 a h
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c996 := derived996 a h
  have h17 : Entails.eval a c222 := h 221 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c631 := derived631 a h
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c997, some c930, some c68, some c996, some c10, some c976, some c265, some c164, some c706, some c170, some c222, some c204, some c60, some c124, some c333, some c296, some c182, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 57) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c32, c997, c930, c68, c996, c10, c976, c265, c164, c706, c170, c222, c204, c60, c124, c333, c296, c182] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c996 := derived996 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c976 := derived976 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c706 := derived706 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c782, some c207, some c124, some c317, some c290, some c278, some c759, some c333, some c246, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c782, c207, c124, c317, c290, c278, c759, c333, c246] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c782 := derived782 a h
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c759 := derived759 a h
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c32, some c782, some c226, some c10, some c207, some c213, some c272, some c767, some c274, some c999, some c60, some c48, some c313, some c348, some c49, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c359, c32, c782, c226, c10, c207, c213, c272, c767, c274, c999, c60, c48, c313, c348, c49] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c782 := derived782 a h
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c767 := derived767 a h
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c999 := derived999 a h
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c313 := h 312 (by decide)
  have h14 : Entails.eval a c348 := h 347 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c139, some c207, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c137, c139, c207] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c997, some c876, some c930, some c32, some c998, some c353, some c65, some c1000, some c265, some c267, some c33, some c106, some c1001, some c4, some c141, some c211, some c60, some c64, some c317, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c69, c997, c876, c930, c32, c998, c353, c65, c1000, c265, c267, c33, c106, c1001, c4, c141, c211, c60, c64, c317] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c998 := derived998 a h
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c1000 := derived1000 a h
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c1001 := derived1001 a h
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c208, some c136, some c267, some c35, some c1001, some c106, some c4, some c34, some c141, some c215, some c211, some c64, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c125, c208, c136, c267, c35, c1001, c106, c4, c34, c141, c215, c211, c64] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨21, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c209, some c49, some c350, some c51, some c315, some c63, some c106, some c442, some c62, some c215, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c265, c209, c49, c350, c51, c315, c63, c106, c442, c62, c215] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c442 := derived442 a h
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c767, some c1003, some c265, some c136, some c1004, some c141, some c274, some c203, some c316, some c137, some c157, some c216, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c353, c767, c1003, c265, c136, c1004, c141, c274, c203, c316, c137, c157, c216] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c767 := derived767 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c1004 := derived1004 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c997, some c876, some c930, some c1002, some c9, some c111, some c867, some c767, some c359, some c353, some c65, some c1005, some c782, some c226, some c208, some c213, some c136, some c274, some c272, some c999, some c156, some c315, some c313, some c63, some c157, some c432, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c69, c997, c876, c930, c1002, c9, c111, c867, c767, c359, c353, c65, c1005, c782, c226, c208, c213, c136, c274, c272, c999, c156, c315, c313, c63, c157, c432] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c1002 := derived1002 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c867 := derived867 a h
  have h8 : Entails.eval a c767 := derived767 a h
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c1005 := derived1005 a h
  have h13 : Entails.eval a c782 := derived782 a h
  have h14 : Entails.eval a c226 := h 225 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c136 := h 135 (by decide)
  have h18 : Entails.eval a c274 := h 273 (by decide)
  have h19 : Entails.eval a c272 := h 271 (by decide)
  have h20 : Entails.eval a c999 := derived999 a h
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c315 := h 314 (by decide)
  have h23 : Entails.eval a c313 := h 312 (by decide)
  have h24 : Entails.eval a c63 := h 62 (by decide)
  have h25 : Entails.eval a c157 := h 156 (by decide)
  have h26 : Entails.eval a c432 := derived432 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1007 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c353, some c226, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1007 : lratChecker f1007 p1007 = .success := by decide +kernel
theorem unsat1007 : Unsatisfiable (PosFin 57) f1007 := by
  apply lratCheckerSound f1007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1007
  · intro a ha; simp [p1007] at ha; subst a; trivial
  · exact checked1007
theorem derived1007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1007 := by
  apply localUnsat_implies_entails f1007 [c359, c353, c226] c1007 unsat1007 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1008 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c876, some c1006, some c269, some c268, some c930, some c870, some c69, some c1007, some c867, some c68, some c60, some c48, some c10, some c254, some c145, some c117, some c706, some c97, some c313, some c320, some c222, some c170, some c55, some c442, some c140, some c928, some c61, some c195, some c306, some c318, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1008 : lratChecker f1008 p1008 = .success := by decide +kernel
theorem unsat1008 : Unsatisfiable (PosFin 57) f1008 := by
  apply lratCheckerSound f1008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1008
  · intro a ha; simp [p1008] at ha; subst a; trivial
  · exact checked1008
theorem derived1008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1008 := by
  apply localUnsat_implies_entails f1008 [c997, c876, c1006, c269, c268, c930, c870, c69, c1007, c867, c68, c60, c48, c10, c254, c145, c117, c706, c97, c313, c320, c222, c170, c55, c442, c140, c928, c61, c195, c306, c318] c1008 unsat1008 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c876 := derived876 a h
  have h2 : Entails.eval a c1006 := derived1006 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c870 := derived870 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c1007 := derived1007 a h
  have h9 : Entails.eval a c867 := derived867 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c10 := h 9 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c706 := derived706 a h
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c313 := h 312 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  have h21 : Entails.eval a c222 := h 221 (by decide)
  have h22 : Entails.eval a c170 := h 169 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c442 := derived442 a h
  have h25 : Entails.eval a c140 := h 139 (by decide)
  have h26 : Entails.eval a c928 := derived928 a h
  have h27 : Entails.eval a c61 := h 60 (by decide)
  have h28 : Entails.eval a c195 := h 194 (by decide)
  have h29 : Entails.eval a c306 := h 305 (by decide)
  have h30 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1009 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1008, some c997, some c876, some c1006, some c269, some c930, some c870, some c867, some c68, some c60, some c48, some c10, some c254, some c164, some c145, some c117, some c97, some c204, some c313, some c320, some c265, some c55, some c151, some c442, some c36, some c61, some c2, some c318, some c170, some c140, some c928, some c195, some c306, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1009 : lratChecker f1009 p1009 = .success := by decide +kernel
theorem unsat1009 : Unsatisfiable (PosFin 57) f1009 := by
  apply lratCheckerSound f1009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1009
  · intro a ha; simp [p1009] at ha; subst a; trivial
  · exact checked1009
theorem derived1009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1009 := by
  apply localUnsat_implies_entails f1009 [c1008, c997, c876, c1006, c269, c930, c870, c867, c68, c60, c48, c10, c254, c164, c145, c117, c97, c204, c313, c320, c265, c55, c151, c442, c36, c61, c2, c318, c170, c140, c928, c195, c306] c1009 unsat1009 (by rfl) a
  have h0 : Entails.eval a c1008 := derived1008 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c870 := derived870 a h
  have h7 : Entails.eval a c867 := derived867 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c164 := h 163 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c97 := h 96 (by decide)
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c320 := h 319 (by decide)
  have h20 : Entails.eval a c265 := h 264 (by decide)
  have h21 : Entails.eval a c55 := h 54 (by decide)
  have h22 : Entails.eval a c151 := h 150 (by decide)
  have h23 : Entails.eval a c442 := derived442 a h
  have h24 : Entails.eval a c36 := h 35 (by decide)
  have h25 : Entails.eval a c61 := h 60 (by decide)
  have h26 : Entails.eval a c2 := h 1 (by decide)
  have h27 : Entails.eval a c318 := h 317 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c140 := h 139 (by decide)
  have h30 : Entails.eval a c928 := derived928 a h
  have h31 : Entails.eval a c195 := h 194 (by decide)
  have h32 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1010 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c60, some c48, some c928, some c61, some c348, some c318, some c315, some c310, some c274, some c320, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1010 : lratChecker f1010 p1010 = .success := by decide +kernel
theorem unsat1010 : Unsatisfiable (PosFin 57) f1010 := by
  apply lratCheckerSound f1010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1010
  · intro a ha; simp [p1010] at ha; subst a; trivial
  · exact checked1010
theorem derived1010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1010 := by
  apply localUnsat_implies_entails f1010 [c359, c60, c48, c928, c61, c348, c318, c315, c310, c274, c320] c1010 unsat1010 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c928 := derived928 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1011 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨1, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c265, some c442, some c36, some c1010, some c9, some c111, some c1004, some c141, some c2, some c126, some c140, some c333, some c203, some c157, some c181, some c216, some c335, some c24, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1011 : lratChecker f1011 p1011 = .success := by decide +kernel
theorem unsat1011 : Unsatisfiable (PosFin 57) f1011 := by
  apply lratCheckerSound f1011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1011
  · intro a ha; simp [p1011] at ha; subst a; trivial
  · exact checked1011
theorem derived1011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1011 := by
  apply localUnsat_implies_entails f1011 [c353, c265, c442, c36, c1010, c9, c111, c1004, c141, c2, c126, c140, c333, c203, c157, c181, c216, c335, c24] c1011 unsat1011 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c442 := derived442 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c1010 := derived1010 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1004 := derived1004 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c181 := h 180 (by decide)
  have h16 : Entails.eval a c216 := h 215 (by decide)
  have h17 : Entails.eval a c335 := h 334 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1012 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c1010, some c111, some c35, some c216, some c52, some c44, some c256, some c352, some c97, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1012 : lratChecker f1012 p1012 = .success := by decide +kernel
theorem unsat1012 : Unsatisfiable (PosFin 57) f1012 := by
  apply lratCheckerSound f1012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1012
  · intro a ha; simp [p1012] at ha; subst a; trivial
  · exact checked1012
theorem derived1012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1012 := by
  apply localUnsat_implies_entails f1012 [c353, c1010, c111, c35, c216, c52, c44, c256, c352, c97] c1012 unsat1012 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c1010 := derived1010 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1013 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c997, some c876, some c930, some c1006, some c870, some c268, some c269, some c1008, some c1009, some c359, some c353, some c230, some c65, some c1011, some c1012, some c106, some c442, some c34, some c267, some c10, some c111, some c138, some c139, some c60, some c202, some c211, some c141, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1013 : lratChecker f1013 p1013 = .success := by decide +kernel
theorem unsat1013 : Unsatisfiable (PosFin 57) f1013 := by
  apply lratCheckerSound f1013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1013
  · intro a ha; simp [p1013] at ha; subst a; trivial
  · exact checked1013
theorem derived1013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1013 := by
  apply localUnsat_implies_entails f1013 [c69, c997, c876, c930, c1006, c870, c268, c269, c1008, c1009, c359, c353, c230, c65, c1011, c1012, c106, c442, c34, c267, c10, c111, c138, c139, c60, c202, c211, c141] c1013 unsat1013 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c1006 := derived1006 a h
  have h5 : Entails.eval a c870 := derived870 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c1008 := derived1008 a h
  have h9 : Entails.eval a c1009 := derived1009 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c1011 := derived1011 a h
  have h15 : Entails.eval a c1012 := derived1012 a h
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c442 := derived442 a h
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c111 := h 110 (by decide)
  have h22 : Entails.eval a c138 := h 137 (by decide)
  have h23 : Entails.eval a c139 := h 138 (by decide)
  have h24 : Entails.eval a c60 := h 59 (by decide)
  have h25 : Entails.eval a c202 := h 201 (by decide)
  have h26 : Entails.eval a c211 := h 210 (by decide)
  have h27 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1014 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨36, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c144, some c9, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1014 : lratChecker f1014 p1014 = .success := by decide +kernel
theorem unsat1014 : Unsatisfiable (PosFin 57) f1014 := by
  apply lratCheckerSound f1014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1014
  · intro a ha; simp [p1014] at ha; subst a; trivial
  · exact checked1014
theorem derived1014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1014 := by
  apply localUnsat_implies_entails f1014 [c40, c144, c9] c1014 unsat1014 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1015 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1014, some c214, some c20, some c116, some c9, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1015 : lratChecker f1015 p1015 = .success := by decide +kernel
theorem unsat1015 : Unsatisfiable (PosFin 57) f1015 := by
  apply lratCheckerSound f1015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1015
  · intro a ha; simp [p1015] at ha; subst a; trivial
  · exact checked1015
theorem derived1015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1015 := by
  apply localUnsat_implies_entails f1015 [c1014, c214, c20, c116, c9] c1015 unsat1015 (by rfl) a
  have h0 : Entails.eval a c1014 := derived1014 a h
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1016 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨23, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c242, some c246, some c272, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p1016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1016 : lratChecker f1016 p1016 = .success := by decide +kernel
theorem unsat1016 : Unsatisfiable (PosFin 57) f1016 := by
  apply lratCheckerSound f1016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1016
  · intro a ha; simp [p1016] at ha; subst a; trivial
  · exact checked1016
theorem derived1016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1016 := by
  apply localUnsat_implies_entails f1016 [c242, c246, c272] c1016 unsat1016 (by rfl) a
  have h0 : Entails.eval a c242 := h 241 (by decide)
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1017 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨35, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c789, some c24, some c265, some c272, some c354, some c226, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1017 : lratChecker f1017 p1017 = .success := by decide +kernel
theorem unsat1017 : Unsatisfiable (PosFin 57) f1017 := by
  apply lratCheckerSound f1017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1017
  · intro a ha; simp [p1017] at ha; subst a; trivial
  · exact checked1017
theorem derived1017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1017 := by
  apply localUnsat_implies_entails f1017 [c107, c789, c24, c265, c272, c354, c226] c1017 unsat1017 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c789 := derived789 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1018 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c9, some c124, some c85, some c930, some c876, some c1015, some c1013, some c11, some c136, some c112, some c68, some c767, some c359, some c316, some c317, some c278, some c333, some c1016, some c270, some c137, some c1017, some c65, some c353, some c354, some c747, some c702, some c279, some c231, some c206, some c272, some c184, some c247, some c300, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1018 : lratChecker f1018 p1018 = .success := by decide +kernel
theorem unsat1018 : Unsatisfiable (PosFin 57) f1018 := by
  apply lratCheckerSound f1018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1018
  · intro a ha; simp [p1018] at ha; subst a; trivial
  · exact checked1018
theorem derived1018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1018 := by
  apply localUnsat_implies_entails f1018 [c997, c9, c124, c85, c930, c876, c1015, c1013, c11, c136, c112, c68, c767, c359, c316, c317, c278, c333, c1016, c270, c137, c1017, c65, c353, c354, c747, c702, c279, c231, c206, c272, c184, c247, c300] c1018 unsat1018 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c876 := derived876 a h
  have h6 : Entails.eval a c1015 := derived1015 a h
  have h7 : Entails.eval a c1013 := derived1013 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c767 := derived767 a h
  have h13 : Entails.eval a c359 := h 358 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c278 := h 277 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c1016 := derived1016 a h
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c1017 := derived1017 a h
  have h22 : Entails.eval a c65 := h 64 (by decide)
  have h23 : Entails.eval a c353 := h 352 (by decide)
  have h24 : Entails.eval a c354 := h 353 (by decide)
  have h25 : Entails.eval a c747 := derived747 a h
  have h26 : Entails.eval a c702 := derived702 a h
  have h27 : Entails.eval a c279 := h 278 (by decide)
  have h28 : Entails.eval a c231 := h 230 (by decide)
  have h29 : Entails.eval a c206 := h 205 (by decide)
  have h30 : Entails.eval a c272 := h 271 (by decide)
  have h31 : Entails.eval a c184 := h 183 (by decide)
  have h32 : Entails.eval a c247 := h 246 (by decide)
  have h33 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1019 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1013, some c112, some c68, some c359, some c11, some c333, some c1017, some c65, some c354, some c747, some c231, some c206, some c213, some c272, some c184, some c279, some c247, some c300, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1019 : lratChecker f1019 p1019 = .success := by decide +kernel
theorem unsat1019 : Unsatisfiable (PosFin 57) f1019 := by
  apply lratCheckerSound f1019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1019
  · intro a ha; simp [p1019] at ha; subst a; trivial
  · exact checked1019
theorem derived1019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1019 := by
  apply localUnsat_implies_entails f1019 [c930, c997, c876, c1015, c1013, c112, c68, c359, c11, c333, c1017, c65, c354, c747, c231, c206, c213, c272, c184, c279, c247, c300] c1019 unsat1019 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c1017 := derived1017 a h
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c747 := derived747 a h
  have h14 : Entails.eval a c231 := h 230 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c279 := h 278 (by decide)
  have h20 : Entails.eval a c247 := h 246 (by decide)
  have h21 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1020 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c9, some c930, some c876, some c1015, some c1013, some c11, some c1018, some c156, some c136, some c112, some c68, some c767, some c124, some c137, some c1019, some c786, some c202, some c206, some c747, some c161, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1020 : lratChecker f1020 p1020 = .success := by decide +kernel
theorem unsat1020 : Unsatisfiable (PosFin 57) f1020 := by
  apply lratCheckerSound f1020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1020
  · intro a ha; simp [p1020] at ha; subst a; trivial
  · exact checked1020
theorem derived1020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1020 := by
  apply localUnsat_implies_entails f1020 [c997, c9, c930, c876, c1015, c1013, c11, c1018, c156, c136, c112, c68, c767, c124, c137, c1019, c786, c202, c206, c747, c161] c1020 unsat1020 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c876 := derived876 a h
  have h4 : Entails.eval a c1015 := derived1015 a h
  have h5 : Entails.eval a c1013 := derived1013 a h
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1018 := derived1018 a h
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c767 := derived767 a h
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c1019 := derived1019 a h
  have h16 : Entails.eval a c786 := derived786 a h
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c747 := derived747 a h
  have h20 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1021 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1013, some c112, some c68, some c11, some c9, some c124, some c767, some c136, some c85, some c1018, some c1020, some c216, some c270, some c267, some c157, some c1016, some c631, some c333, some c202, some c786, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1021 : lratChecker f1021 p1021 = .success := by decide +kernel
theorem unsat1021 : Unsatisfiable (PosFin 57) f1021 := by
  apply lratCheckerSound f1021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1021
  · intro a ha; simp [p1021] at ha; subst a; trivial
  · exact checked1021
theorem derived1021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1021 := by
  apply localUnsat_implies_entails f1021 [c930, c997, c876, c1015, c1013, c112, c68, c11, c9, c124, c767, c136, c85, c1018, c1020, c216, c270, c267, c157, c1016, c631, c333, c202, c786] c1021 unsat1021 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c767 := derived767 a h
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c1018 := derived1018 a h
  have h14 : Entails.eval a c1020 := derived1020 a h
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c1016 := derived1016 a h
  have h20 : Entails.eval a c631 := derived631 a h
  have h21 : Entails.eval a c333 := h 332 (by decide)
  have h22 : Entails.eval a c202 := h 201 (by decide)
  have h23 : Entails.eval a c786 := derived786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1022 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨35, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c786, some c22, some c230, some c213, some c278, some c317, some c318, some c61, some c157, some c15, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1022 : lratChecker f1022 p1022 = .success := by decide +kernel
theorem unsat1022 : Unsatisfiable (PosFin 57) f1022 := by
  apply lratCheckerSound f1022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1022
  · intro a ha; simp [p1022] at ha; subst a; trivial
  · exact checked1022
theorem derived1022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1022 := by
  apply localUnsat_implies_entails f1022 [c786, c22, c230, c213, c278, c317, c318, c61, c157, c15] c1022 unsat1022 (by rfl) a
  have h0 : Entails.eval a c786 := derived786 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1023 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨37, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c136, some c767, some c124, some c1015, some c359, some c1022, some c333, some c1016, some c126, some c246, some c87, some c374, some c265, some c272, some c177, some c1007, some c226, some c206, some c702, some c354, some c685, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1023 : lratChecker f1023 p1023 = .success := by decide +kernel
theorem unsat1023 : Unsatisfiable (PosFin 57) f1023 := by
  apply lratCheckerSound f1023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1023
  · intro a ha; simp [p1023] at ha; subst a; trivial
  · exact checked1023
theorem derived1023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1023 := by
  apply localUnsat_implies_entails f1023 [c11, c136, c767, c124, c1015, c359, c1022, c333, c1016, c126, c246, c87, c374, c265, c272, c177, c1007, c226, c206, c702, c354, c685] c1023 unsat1023 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c767 := derived767 a h
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c1015 := derived1015 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c1022 := derived1022 a h
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c1016 := derived1016 a h
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c374 := h 373 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c1007 := derived1007 a h
  have h17 : Entails.eval a c226 := h 225 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c702 := derived702 a h
  have h20 : Entails.eval a c354 := h 353 (by decide)
  have h21 : Entails.eval a c685 := derived685 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1024 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1021, some c930, some c997, some c876, some c1015, some c1013, some c112, some c68, some c11, some c124, some c767, some c136, some c1023, some c270, some c33, some c137, some c107, some c65, some c353, some c747, some c702, some c206, some c1019, some c786, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1024 : lratChecker f1024 p1024 = .success := by decide +kernel
theorem unsat1024 : Unsatisfiable (PosFin 57) f1024 := by
  apply lratCheckerSound f1024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1024
  · intro a ha; simp [p1024] at ha; subst a; trivial
  · exact checked1024
theorem derived1024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1024 := by
  apply localUnsat_implies_entails f1024 [c1021, c930, c997, c876, c1015, c1013, c112, c68, c11, c124, c767, c136, c1023, c270, c33, c137, c107, c65, c353, c747, c702, c206, c1019, c786] c1024 unsat1024 (by rfl) a
  have h0 : Entails.eval a c1021 := derived1021 a h
  have h1 : Entails.eval a c930 := derived930 a h
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c876 := derived876 a h
  have h4 : Entails.eval a c1015 := derived1015 a h
  have h5 : Entails.eval a c1013 := derived1013 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c767 := derived767 a h
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c1023 := derived1023 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c747 := derived747 a h
  have h20 : Entails.eval a c702 := derived702 a h
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c1019 := derived1019 a h
  have h23 : Entails.eval a c786 := derived786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1025 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1013, some c112, some c68, some c359, some c11, some c1021, some c1024, some c204, some c207, some c165, some c747, some c65, some c161, some c782, some c107, some c33, some c216, some c270, some c267, some c513, some c127, some c140, some c336, some c334, some c202, some c183, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1025 : lratChecker f1025 p1025 = .success := by decide +kernel
theorem unsat1025 : Unsatisfiable (PosFin 57) f1025 := by
  apply lratCheckerSound f1025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1025
  · intro a ha; simp [p1025] at ha; subst a; trivial
  · exact checked1025
theorem derived1025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1025 := by
  apply localUnsat_implies_entails f1025 [c930, c997, c876, c1015, c1013, c112, c68, c359, c11, c1021, c1024, c204, c207, c165, c747, c65, c161, c782, c107, c33, c216, c270, c267, c513, c127, c140, c336, c334, c202, c183] c1025 unsat1025 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c1021 := derived1021 a h
  have h10 : Entails.eval a c1024 := derived1024 a h
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c747 := derived747 a h
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c782 := derived782 a h
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c216 := h 215 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  have h23 : Entails.eval a c513 := derived513 a h
  have h24 : Entails.eval a c127 := h 126 (by decide)
  have h25 : Entails.eval a c140 := h 139 (by decide)
  have h26 : Entails.eval a c336 := h 335 (by decide)
  have h27 : Entails.eval a c334 := h 333 (by decide)
  have h28 : Entails.eval a c202 := h 201 (by decide)
  have h29 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1026 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨20, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c348, some c254, some c96, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1026 : lratChecker f1026 p1026 = .success := by decide +kernel
theorem unsat1026 : Unsatisfiable (PosFin 57) f1026 := by
  apply lratCheckerSound f1026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1026
  · intro a ha; simp [p1026] at ha; subst a; trivial
  · exact checked1026
theorem derived1026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1026 := by
  apply localUnsat_implies_entails f1026 [c348, c254, c96] c1026 unsat1026 (by rfl) a
  have h0 : Entails.eval a c348 := h 347 (by decide)
  have h1 : Entails.eval a c254 := h 253 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1027 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c315, some c35, some c303, some c249, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1027 : lratChecker f1027 p1027 = .success := by decide +kernel
theorem unsat1027 : Unsatisfiable (PosFin 57) f1027 := by
  apply lratCheckerSound f1027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1027
  · intro a ha; simp [p1027] at ha; subst a; trivial
  · exact checked1027
theorem derived1027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1027 := by
  apply localUnsat_implies_entails f1027 [c216, c315, c35, c303, c249] c1027 unsat1027 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1028 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c1025, some c870, some c876, some c1015, some c1013, some c11, some c112, some c68, some c1026, some c48, some c9, some c156, some c269, some c268, some c359, some c617, some c65, some c226, some c107, some c1027, some c157, some c63, some c202, some c313, some c151, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1028 : lratChecker f1028 p1028 = .success := by decide +kernel
theorem unsat1028 : Unsatisfiable (PosFin 57) f1028 := by
  apply lratCheckerSound f1028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1028
  · intro a ha; simp [p1028] at ha; subst a; trivial
  · exact checked1028
theorem derived1028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1028 := by
  apply localUnsat_implies_entails f1028 [c930, c997, c1025, c870, c876, c1015, c1013, c11, c112, c68, c1026, c48, c9, c156, c269, c268, c359, c617, c65, c226, c107, c1027, c157, c63, c202, c313, c151] c1028 unsat1028 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c1025 := derived1025 a h
  have h3 : Entails.eval a c870 := derived870 a h
  have h4 : Entails.eval a c876 := derived876 a h
  have h5 : Entails.eval a c1015 := derived1015 a h
  have h6 : Entails.eval a c1013 := derived1013 a h
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c1026 := derived1026 a h
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c617 := derived617 a h
  have h18 : Entails.eval a c65 := h 64 (by decide)
  have h19 : Entails.eval a c226 := h 225 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c1027 := derived1027 a h
  have h22 : Entails.eval a c157 := h 156 (by decide)
  have h23 : Entails.eval a c63 := h 62 (by decide)
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c313 := h 312 (by decide)
  have h26 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1029 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨23, by decide⟩, false), (⟨38, by decide⟩, false), (⟨19, by decide⟩, true), (⟨35, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c226, some c1017, some c267, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1029 : lratChecker f1029 p1029 = .success := by decide +kernel
theorem unsat1029 : Unsatisfiable (PosFin 57) f1029 := by
  apply lratCheckerSound f1029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1029
  · intro a ha; simp [p1029] at ha; subst a; trivial
  · exact checked1029
theorem derived1029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1029 := by
  apply localUnsat_implies_entails f1029 [c65, c226, c1017, c267] c1029 unsat1029 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c226 := h 225 (by decide)
  have h2 : Entails.eval a c1017 := derived1017 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1030 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c876, some c930, some c1015, some c1013, some c112, some c68, some c1025, some c1026, some c359, some c269, some c268, some c230, some c11, some c1028, some c126, some c140, some c333, some c1029, some c337, some c541, some c363, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1030 : lratChecker f1030 p1030 = .success := by decide +kernel
theorem unsat1030 : Unsatisfiable (PosFin 57) f1030 := by
  apply lratCheckerSound f1030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1030
  · intro a ha; simp [p1030] at ha; subst a; trivial
  · exact checked1030
theorem derived1030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1030 := by
  apply localUnsat_implies_entails f1030 [c997, c876, c930, c1015, c1013, c112, c68, c1025, c1026, c359, c269, c268, c230, c11, c1028, c126, c140, c333, c1029, c337, c541, c363] c1030 unsat1030 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c876 := derived876 a h
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c1025 := derived1025 a h
  have h8 : Entails.eval a c1026 := derived1026 a h
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c1028 := derived1028 a h
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c1029 := derived1029 a h
  have h19 : Entails.eval a c337 := h 336 (by decide)
  have h20 : Entails.eval a c541 := derived541 a h
  have h21 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1031 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1013, some c112, some c11, some c68, some c359, some c1025, some c870, some c268, some c269, some c230, some c1026, some c48, some c9, some c156, some c1030, some c49, some c320, some c313, some c274, some c354, some c231, some c279, some c216, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1031 : lratChecker f1031 p1031 = .success := by decide +kernel
theorem unsat1031 : Unsatisfiable (PosFin 57) f1031 := by
  apply lratCheckerSound f1031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1031
  · intro a ha; simp [p1031] at ha; subst a; trivial
  · exact checked1031
theorem derived1031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1031 := by
  apply localUnsat_implies_entails f1031 [c930, c997, c876, c1015, c1013, c112, c11, c68, c359, c1025, c870, c268, c269, c230, c1026, c48, c9, c156, c1030, c49, c320, c313, c274, c354, c231, c279, c216] c1031 unsat1031 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c1025 := derived1025 a h
  have h10 : Entails.eval a c870 := derived870 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c1026 := derived1026 a h
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c1030 := derived1030 a h
  have h19 : Entails.eval a c49 := h 48 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c274 := h 273 (by decide)
  have h23 : Entails.eval a c354 := h 353 (by decide)
  have h24 : Entails.eval a c231 := h 230 (by decide)
  have h25 : Entails.eval a c279 := h 278 (by decide)
  have h26 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1032 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨1, by decide⟩, true), (⟨33, by decide⟩, false), (⟨4, by decide⟩, true), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c349, some c338, some c95, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p1032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1032 : lratChecker f1032 p1032 = .success := by decide +kernel
theorem unsat1032 : Unsatisfiable (PosFin 57) f1032 := by
  apply lratCheckerSound f1032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1032
  · intro a ha; simp [p1032] at ha; subst a; trivial
  · exact checked1032
theorem derived1032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1032 := by
  apply localUnsat_implies_entails f1032 [c349, c338, c95] c1032 unsat1032 (by rfl) a
  have h0 : Entails.eval a c349 := h 348 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1033 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c355, some c41, some c75, some c110, some c107, some c74, some c1032, some c50, some c317, some c55, some c937, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1033 : lratChecker f1033 p1033 = .success := by decide +kernel
theorem unsat1033 : Unsatisfiable (PosFin 57) f1033 := by
  apply lratCheckerSound f1033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1033
  · intro a ha; simp [p1033] at ha; subst a; trivial
  · exact checked1033
theorem derived1033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1033 := by
  apply localUnsat_implies_entails f1033 [c353, c355, c41, c75, c110, c107, c74, c1032, c50, c317, c55, c937] c1033 unsat1033 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c1032 := derived1032 a h
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c937 := derived937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1034 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c37, some c209, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1034 : lratChecker f1034 p1034 = .success := by decide +kernel
theorem unsat1034 : Unsatisfiable (PosFin 57) f1034 := by
  apply lratCheckerSound f1034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1034
  · intro a ha; simp [p1034] at ha; subst a; trivial
  · exact checked1034
theorem derived1034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1034 := by
  apply localUnsat_implies_entails f1034 [c17, c37, c209] c1034 unsat1034 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1035 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨37, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c313, some c156, some c317, some c931, some c938, some c50, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1035 : lratChecker f1035 p1035 = .success := by decide +kernel
theorem unsat1035 : Unsatisfiable (PosFin 57) f1035 := by
  apply lratCheckerSound f1035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1035
  · intro a ha; simp [p1035] at ha; subst a; trivial
  · exact checked1035
theorem derived1035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1035 := by
  apply localUnsat_implies_entails f1035 [c41, c313, c156, c317, c931, c938, c50] c1035 unsat1035 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c931 := derived931 a h
  have h5 : Entails.eval a c938 := derived938 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1036 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨35, by decide⟩, false), (⟨25, by decide⟩, true), (⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1031, some c108, some c930, some c997, some c876, some c1015, some c879, some c870, some c48, some c928, some c345, some c306, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1036 : lratChecker f1036 p1036 = .success := by decide +kernel
theorem unsat1036 : Unsatisfiable (PosFin 57) f1036 := by
  apply lratCheckerSound f1036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1036
  · intro a ha; simp [p1036] at ha; subst a; trivial
  · exact checked1036
theorem derived1036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1036 := by
  apply localUnsat_implies_entails f1036 [c1031, c108, c930, c997, c876, c1015, c879, c870, c48, c928, c345, c306] c1036 unsat1036 (by rfl) a
  have h0 : Entails.eval a c1031 := derived1031 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c997 := derived997 a h
  have h4 : Entails.eval a c876 := derived876 a h
  have h5 : Entails.eval a c1015 := derived1015 a h
  have h6 : Entails.eval a c879 := derived879 a h
  have h7 : Entails.eval a c870 := derived870 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c928 := derived928 a h
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1037 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c318, some c61, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1037 : lratChecker f1037 p1037 = .success := by decide +kernel
theorem unsat1037 : Unsatisfiable (PosFin 57) f1037 := by
  apply lratCheckerSound f1037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1037
  · intro a ha; simp [p1037] at ha; subst a; trivial
  · exact checked1037
theorem derived1037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1037 := by
  apply localUnsat_implies_entails f1037 [c317, c318, c61] c1037 unsat1037 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1038 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨30, by decide⟩, true), (⟨1, by decide⟩, false), (⟨37, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c74, some c2, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1038 : lratChecker f1038 p1038 = .success := by decide +kernel
theorem unsat1038 : Unsatisfiable (PosFin 57) f1038 := by
  apply lratCheckerSound f1038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1038
  · intro a ha; simp [p1038] at ha; subst a; trivial
  · exact checked1038
theorem derived1038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1038 := by
  apply localUnsat_implies_entails f1038 [c146, c74, c2] c1038 unsat1038 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1039 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c1031, some c5, some c930, some c876, some c1015, some c108, some c112, some c11, some c165, some c1033, some c161, some c41, some c21, some c164, some c207, some c892, some c1034, some c107, some c1037, some c1038, some c1035, some c1036, some c274, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1039 : lratChecker f1039 p1039 = .success := by decide +kernel
theorem unsat1039 : Unsatisfiable (PosFin 57) f1039 := by
  apply lratCheckerSound f1039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1039
  · intro a ha; simp [p1039] at ha; subst a; trivial
  · exact checked1039
theorem derived1039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1039 := by
  apply localUnsat_implies_entails f1039 [c997, c1031, c5, c930, c876, c1015, c108, c112, c11, c165, c1033, c161, c41, c21, c164, c207, c892, c1034, c107, c1037, c1038, c1035, c1036, c274] c1039 unsat1039 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c876 := derived876 a h
  have h5 : Entails.eval a c1015 := derived1015 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c1033 := derived1033 a h
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c892 := derived892 a h
  have h17 : Entails.eval a c1034 := derived1034 a h
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c1037 := derived1037 a h
  have h20 : Entails.eval a c1038 := derived1038 a h
  have h21 : Entails.eval a c1035 := derived1035 a h
  have h22 : Entails.eval a c1036 := derived1036 a h
  have h23 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1040 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨36, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c1037, some c316, some c48, some c348, some c946, some c49, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1040 : lratChecker f1040 p1040 = .success := by decide +kernel
theorem unsat1040 : Unsatisfiable (PosFin 57) f1040 := by
  apply lratCheckerSound f1040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1040
  · intro a ha; simp [p1040] at ha; subst a; trivial
  · exact checked1040
theorem derived1040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1040 := by
  apply localUnsat_implies_entails f1040 [c107, c1037, c316, c48, c348, c946, c49] c1040 unsat1040 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c1037 := derived1037 a h
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c946 := derived946 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1041 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c63, some c62, some c315, some c2, some c160, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1041 : lratChecker f1041 p1041 = .success := by decide +kernel
theorem unsat1041 : Unsatisfiable (PosFin 57) f1041 := by
  apply lratCheckerSound f1041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1041
  · intro a ha; simp [p1041] at ha; subst a; trivial
  · exact checked1041
theorem derived1041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1041 := by
  apply localUnsat_implies_entails f1041 [c63, c62, c315, c2, c160] c1041 unsat1041 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1042 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c107, some c1037, some c1040, some c274, some c278, some c1041, some c313, some c160, some c2, some c50, some c928, some c349, some c214, some c101, some c33, some c351, some c216, some c513, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1042 : lratChecker f1042 p1042 = .success := by decide +kernel
theorem unsat1042 : Unsatisfiable (PosFin 57) f1042 := by
  apply lratCheckerSound f1042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1042
  · intro a ha; simp [p1042] at ha; subst a; trivial
  · exact checked1042
theorem derived1042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1042 := by
  apply localUnsat_implies_entails f1042 [c359, c107, c1037, c1040, c274, c278, c1041, c313, c160, c2, c50, c928, c349, c214, c101, c33, c351, c216, c513] c1042 unsat1042 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1037 := derived1037 a h
  have h3 : Entails.eval a c1040 := derived1040 a h
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c1041 := derived1041 a h
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c928 := derived928 a h
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c351 := h 350 (by decide)
  have h17 : Entails.eval a c216 := h 215 (by decide)
  have h18 : Entails.eval a c513 := derived513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1043 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨38, by decide⟩, false), (⟨30, by decide⟩, true), (⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c216, some c44, some c52, some c351, some c352, some c312, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1043 : lratChecker f1043 p1043 = .success := by decide +kernel
theorem unsat1043 : Unsatisfiable (PosFin 57) f1043 := by
  apply lratCheckerSound f1043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1043
  · intro a ha; simp [p1043] at ha; subst a; trivial
  · exact checked1043
theorem derived1043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1043 := by
  apply localUnsat_implies_entails f1043 [c35, c216, c44, c52, c351, c352, c312] c1043 unsat1043 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1044 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨38, by decide⟩, false), (⟨30, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c313, some c1034, some c160, some c1043, some c110, some c50, some c349, some c186, some c95, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1044 : lratChecker f1044 p1044 = .success := by decide +kernel
theorem unsat1044 : Unsatisfiable (PosFin 57) f1044 := by
  apply lratCheckerSound f1044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1044
  · intro a ha; simp [p1044] at ha; subst a; trivial
  · exact checked1044
theorem derived1044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1044 := by
  apply localUnsat_implies_entails f1044 [c37, c313, c1034, c160, c1043, c110, c50, c349, c186, c95] c1044 unsat1044 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c1034 := derived1034 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1043 := derived1043 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1045 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨30, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c62, some c348, some c110, some c48, some c95, some c101, some c214, some c252, some c33, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1045 : lratChecker f1045 p1045 = .success := by decide +kernel
theorem unsat1045 : Unsatisfiable (PosFin 57) f1045 := by
  apply lratCheckerSound f1045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1045
  · intro a ha; simp [p1045] at ha; subst a; trivial
  · exact checked1045
theorem derived1045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1045 := by
  apply localUnsat_implies_entails f1045 [c49, c62, c348, c110, c48, c95, c101, c214, c252, c33] c1045 unsat1045 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1046 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨1, by decide⟩, true), (⟨37, by decide⟩, false), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c359, some c1045, some c1034, some c1044, some c42, some c278, some c110, some c316, some c35, some c61, some c216, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1046 : lratChecker f1046 p1046 = .success := by decide +kernel
theorem unsat1046 : Unsatisfiable (PosFin 57) f1046 := by
  apply lratCheckerSound f1046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1046
  · intro a ha; simp [p1046] at ha; subst a; trivial
  · exact checked1046
theorem derived1046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1046 := by
  apply localUnsat_implies_entails f1046 [c17, c359, c1045, c1034, c1044, c42, c278, c110, c316, c35, c61, c216] c1046 unsat1046 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c1045 := derived1045 a h
  have h3 : Entails.eval a c1034 := derived1034 a h
  have h4 : Entails.eval a c1044 := derived1044 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1047 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨37, by decide⟩, false), (⟨26, by decide⟩, false), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1046, some c317, some c215, some c1037, some c48, some c110, some c348, some c34, some c49, some c1034, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1047 : lratChecker f1047 p1047 = .success := by decide +kernel
theorem unsat1047 : Unsatisfiable (PosFin 57) f1047 := by
  apply lratCheckerSound f1047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1047
  · intro a ha; simp [p1047] at ha; subst a; trivial
  · exact checked1047
theorem derived1047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1047 := by
  apply localUnsat_implies_entails f1047 [c1046, c317, c215, c1037, c48, c110, c348, c34, c49, c1034] c1047 unsat1047 (by rfl) a
  have h0 : Entails.eval a c1046 := derived1046 a h
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c1034 := derived1034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1048 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c1031, some c5, some c108, some c930, some c876, some c1015, some c112, some c11, some c165, some c1033, some c161, some c1039, some c1042, some c1047, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1048 : lratChecker f1048 p1048 = .success := by decide +kernel
theorem unsat1048 : Unsatisfiable (PosFin 57) f1048 := by
  apply lratCheckerSound f1048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1048
  · intro a ha; simp [p1048] at ha; subst a; trivial
  · exact checked1048
theorem derived1048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1048 := by
  apply localUnsat_implies_entails f1048 [c997, c1031, c5, c108, c930, c876, c1015, c112, c11, c165, c1033, c161, c1039, c1042, c1047] c1048 unsat1048 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c876 := derived876 a h
  have h6 : Entails.eval a c1015 := derived1015 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c1033 := derived1033 a h
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c1039 := derived1039 a h
  have h13 : Entails.eval a c1042 := derived1042 a h
  have h14 : Entails.eval a c1047 := derived1047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1049 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c21, some c1034, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1049 : lratChecker f1049 p1049 = .success := by decide +kernel
theorem unsat1049 : Unsatisfiable (PosFin 57) f1049 := by
  apply lratCheckerSound f1049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1049
  · intro a ha; simp [p1049] at ha; subst a; trivial
  · exact checked1049
theorem derived1049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1049 := by
  apply localUnsat_implies_entails f1049 [c41, c21, c1034] c1049 unsat1049 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c1034 := derived1034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1050 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1049, some c997, some c1031, some c5, some c161, some c108, some c930, some c876, some c1015, some c165, some c1047, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1050 : lratChecker f1050 p1050 = .success := by decide +kernel
theorem unsat1050 : Unsatisfiable (PosFin 57) f1050 := by
  apply lratCheckerSound f1050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1050
  · intro a ha; simp [p1050] at ha; subst a; trivial
  · exact checked1050
theorem derived1050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1050 := by
  apply localUnsat_implies_entails f1050 [c1049, c997, c1031, c5, c161, c108, c930, c876, c1015, c165, c1047] c1050 unsat1050 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c1031 := derived1031 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c876 := derived876 a h
  have h8 : Entails.eval a c1015 := derived1015 a h
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c1047 := derived1047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1051 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨33, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c17, some c313, some c1034, some c60, some c139, some c214, some c267, some c32, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1051 : lratChecker f1051 p1051 = .success := by decide +kernel
theorem unsat1051 : Unsatisfiable (PosFin 57) f1051 := by
  apply lratCheckerSound f1051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1051
  · intro a ha; simp [p1051] at ha; subst a; trivial
  · exact checked1051
theorem derived1051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1051 := by
  apply localUnsat_implies_entails f1051 [c37, c17, c313, c1034, c60, c139, c214, c267, c32] c1051 unsat1051 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c1034 := derived1034 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1052 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c997, some c1031, some c5, some c108, some c930, some c876, some c1015, some c161, some c17, some c1049, some c1050, some c208, some c203, some c1051, some c1045, some c159, some c318, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1052 : lratChecker f1052 p1052 = .success := by decide +kernel
theorem unsat1052 : Unsatisfiable (PosFin 57) f1052 := by
  apply lratCheckerSound f1052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1052
  · intro a ha; simp [p1052] at ha; subst a; trivial
  · exact checked1052
theorem derived1052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1052 := by
  apply localUnsat_implies_entails f1052 [c1048, c997, c1031, c5, c108, c930, c876, c1015, c161, c17, c1049, c1050, c208, c203, c1051, c1045, c159, c318] c1052 unsat1052 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c1031 := derived1031 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c876 := derived876 a h
  have h7 : Entails.eval a c1015 := derived1015 a h
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c1049 := derived1049 a h
  have h11 : Entails.eval a c1050 := derived1050 a h
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c1051 := derived1051 a h
  have h15 : Entails.eval a c1045 := derived1045 a h
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1053 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨31, by decide⟩, false), (⟨39, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c76, some c110, some c1037, some c146, some c278, some c706, some c320, some c1045, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1053 : lratChecker f1053 p1053 = .success := by decide +kernel
theorem unsat1053 : Unsatisfiable (PosFin 57) f1053 := by
  apply lratCheckerSound f1053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1053
  · intro a ha; simp [p1053] at ha; subst a; trivial
  · exact checked1053
theorem derived1053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1053 := by
  apply localUnsat_implies_entails f1053 [c359, c76, c110, c1037, c146, c278, c706, c320, c1045] c1053 unsat1053 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c706 := derived706 a h
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c1045 := derived1045 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1054 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1052, some c1048, some c997, some c1031, some c5, some c108, some c930, some c876, some c1015, some c208, some c164, some c353, some c702, some c703, some c1053, some c354, some c1032, some c685, some c203, some c631, some c211, some c265, some c267, some c55, some c35, some c317, some c110, some c50, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1054 : lratChecker f1054 p1054 = .success := by decide +kernel
theorem unsat1054 : Unsatisfiable (PosFin 57) f1054 := by
  apply lratCheckerSound f1054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1054
  · intro a ha; simp [p1054] at ha; subst a; trivial
  · exact checked1054
theorem derived1054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1054 := by
  apply localUnsat_implies_entails f1054 [c1052, c1048, c997, c1031, c5, c108, c930, c876, c1015, c208, c164, c353, c702, c703, c1053, c354, c1032, c685, c203, c631, c211, c265, c267, c55, c35, c317, c110, c50] c1054 unsat1054 (by rfl) a
  have h0 : Entails.eval a c1052 := derived1052 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c1031 := derived1031 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c876 := derived876 a h
  have h8 : Entails.eval a c1015 := derived1015 a h
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c702 := derived702 a h
  have h13 : Entails.eval a c703 := derived703 a h
  have h14 : Entails.eval a c1053 := derived1053 a h
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c1032 := derived1032 a h
  have h17 : Entails.eval a c685 := derived685 a h
  have h18 : Entails.eval a c203 := h 202 (by decide)
  have h19 : Entails.eval a c631 := derived631 a h
  have h20 : Entails.eval a c211 := h 210 (by decide)
  have h21 : Entails.eval a c265 := h 264 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c35 := h 34 (by decide)
  have h25 : Entails.eval a c317 := h 316 (by decide)
  have h26 : Entails.eval a c110 := h 109 (by decide)
  have h27 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1055 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c1031, some c5, some c108, some c930, some c876, some c1015, some c1052, some c1054, some c165, some c353, some c355, some c41, some c75, some c110, some c74, some c1032, some c50, some c317, some c55, some c937, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1055 : lratChecker f1055 p1055 = .success := by decide +kernel
theorem unsat1055 : Unsatisfiable (PosFin 57) f1055 := by
  apply lratCheckerSound f1055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1055
  · intro a ha; simp [p1055] at ha; subst a; trivial
  · exact checked1055
theorem derived1055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1055 := by
  apply localUnsat_implies_entails f1055 [c997, c1031, c5, c108, c930, c876, c1015, c1052, c1054, c165, c353, c355, c41, c75, c110, c74, c1032, c50, c317, c55, c937] c1055 unsat1055 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c876 := derived876 a h
  have h6 : Entails.eval a c1015 := derived1015 a h
  have h7 : Entails.eval a c1052 := derived1052 a h
  have h8 : Entails.eval a c1054 := derived1054 a h
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c1032 := derived1032 a h
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c55 := h 54 (by decide)
  have h20 : Entails.eval a c937 := derived937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1056 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c318, some c55, some c313, some c211, some c159, some c631, some c203, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1056 : lratChecker f1056 p1056 = .success := by decide +kernel
theorem unsat1056 : Unsatisfiable (PosFin 57) f1056 := by
  apply lratCheckerSound f1056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1056
  · intro a ha; simp [p1056] at ha; subst a; trivial
  · exact checked1056
theorem derived1056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1056 := by
  apply localUnsat_implies_entails f1056 [c317, c318, c55, c313, c211, c159, c631, c203] c1056 unsat1056 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1057 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c211, some c158, some c706, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1057 : lratChecker f1057 p1057 = .success := by decide +kernel
theorem unsat1057 : Unsatisfiable (PosFin 57) f1057 := by
  apply lratCheckerSound f1057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1057
  · intro a ha; simp [p1057] at ha; subst a; trivial
  · exact checked1057
theorem derived1057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1057 := by
  apply localUnsat_implies_entails f1057 [c313, c211, c158, c706] c1057 unsat1057 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c706 := derived706 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1058 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1031, some c5, some c1055, some c10, some c164, some c359, some c108, some c353, some c702, some c703, some c165, some c1056, some c1057, some c55, some c316, some c214, some c278, some c879, some c1032, some c110, some c50, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1058 : lratChecker f1058 p1058 = .success := by decide +kernel
theorem unsat1058 : Unsatisfiable (PosFin 57) f1058 := by
  apply lratCheckerSound f1058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1058
  · intro a ha; simp [p1058] at ha; subst a; trivial
  · exact checked1058
theorem derived1058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1058 := by
  apply localUnsat_implies_entails f1058 [c930, c997, c876, c1015, c1031, c5, c1055, c10, c164, c359, c108, c353, c702, c703, c165, c1056, c1057, c55, c316, c214, c278, c879, c1032, c110, c50] c1058 unsat1058 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1031 := derived1031 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c1055 := derived1055 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c702 := derived702 a h
  have h13 : Entails.eval a c703 := derived703 a h
  have h14 : Entails.eval a c165 := h 164 (by decide)
  have h15 : Entails.eval a c1056 := derived1056 a h
  have h16 : Entails.eval a c1057 := derived1057 a h
  have h17 : Entails.eval a c55 := h 54 (by decide)
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c214 := h 213 (by decide)
  have h20 : Entails.eval a c278 := h 277 (by decide)
  have h21 : Entails.eval a c879 := derived879 a h
  have h22 : Entails.eval a c1032 := derived1032 a h
  have h23 : Entails.eval a c110 := h 109 (by decide)
  have h24 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1059 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c37, some c997, some c1055, some c10, some c1048, some c1031, some c108, some c876, some c930, some c1051, some c159, some c318, some c315, some c158, some c60, some c64, some c951, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1059 : lratChecker f1059 p1059 = .success := by decide +kernel
theorem unsat1059 : Unsatisfiable (PosFin 57) f1059 := by
  apply lratCheckerSound f1059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1059
  · intro a ha; simp [p1059] at ha; subst a; trivial
  · exact checked1059
theorem derived1059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1059 := by
  apply localUnsat_implies_entails f1059 [c1058, c37, c997, c1055, c10, c1048, c1031, c108, c876, c930, c1051, c159, c318, c315, c158, c60, c64, c951] c1059 unsat1059 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c1055 := derived1055 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c1048 := derived1048 a h
  have h6 : Entails.eval a c1031 := derived1031 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c876 := derived876 a h
  have h9 : Entails.eval a c930 := derived930 a h
  have h10 : Entails.eval a c1051 := derived1051 a h
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c64 := h 63 (by decide)
  have h17 : Entails.eval a c951 := derived951 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1060 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c158, some c313, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1060 : lratChecker f1060 p1060 = .success := by decide +kernel
theorem unsat1060 : Unsatisfiable (PosFin 57) f1060 := by
  apply lratCheckerSound f1060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1060
  · intro a ha; simp [p1060] at ha; subst a; trivial
  · exact checked1060
theorem derived1060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1060 := by
  apply localUnsat_implies_entails f1060 [c160, c158, c313] c1060 unsat1060 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1061 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1048, some c997, some c1031, some c5, some c108, some c876, some c930, some c1055, some c10, some c1058, some c161, some c17, some c37, some c1059, some c203, some c202, some c1060, some c317, some c215, some c60, some c140, some c211, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1061 : lratChecker f1061 p1061 = .success := by decide +kernel
theorem unsat1061 : Unsatisfiable (PosFin 57) f1061 := by
  apply lratCheckerSound f1061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1061
  · intro a ha; simp [p1061] at ha; subst a; trivial
  · exact checked1061
theorem derived1061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1061 := by
  apply localUnsat_implies_entails f1061 [c1048, c997, c1031, c5, c108, c876, c930, c1055, c10, c1058, c161, c17, c37, c1059, c203, c202, c1060, c317, c215, c60, c140, c211] c1061 unsat1061 (by rfl) a
  have h0 : Entails.eval a c1048 := derived1048 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c1031 := derived1031 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c876 := derived876 a h
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c1055 := derived1055 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1058 := derived1058 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c1059 := derived1059 a h
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c1060 := derived1060 a h
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c60 := h 59 (by decide)
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1062 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c211, some c631, some c4, some c157, some c159, some c207, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1062 : lratChecker f1062 p1062 = .success := by decide +kernel
theorem unsat1062 : Unsatisfiable (PosFin 57) f1062 := by
  apply lratCheckerSound f1062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1062
  · intro a ha; simp [p1062] at ha; subst a; trivial
  · exact checked1062
theorem derived1062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1062 := by
  apply localUnsat_implies_entails f1062 [c313, c211, c631, c4, c157, c159, c207] c1062 unsat1062 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1063 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c797, some c102, some c348, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p1063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1063 : lratChecker f1063 p1063 = .success := by decide +kernel
theorem unsat1063 : Unsatisfiable (PosFin 57) f1063 := by
  apply lratCheckerSound f1063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1063
  · intro a ha; simp [p1063] at ha; subst a; trivial
  · exact checked1063
theorem derived1063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1063 := by
  apply localUnsat_implies_entails f1063 [c797, c102, c348] c1063 unsat1063 (by rfl) a
  have h0 : Entails.eval a c797 := derived797 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1064 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1061, some c1048, some c997, some c1031, some c5, some c108, some c930, some c876, some c1015, some c317, some c318, some c215, some c1037, some c48, some c60, some c442, some c110, some c22, some c928, some c1062, some c1063, some c10, some c164, some c359, some c353, some c161, some c274, some c4, some c320, some c159, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1064 : lratChecker f1064 p1064 = .success := by decide +kernel
theorem unsat1064 : Unsatisfiable (PosFin 57) f1064 := by
  apply lratCheckerSound f1064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1064
  · intro a ha; simp [p1064] at ha; subst a; trivial
  · exact checked1064
theorem derived1064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1064 := by
  apply localUnsat_implies_entails f1064 [c1061, c1048, c997, c1031, c5, c108, c930, c876, c1015, c317, c318, c215, c1037, c48, c60, c442, c110, c22, c928, c1062, c1063, c10, c164, c359, c353, c161, c274, c4, c320, c159] c1064 unsat1064 (by rfl) a
  have h0 : Entails.eval a c1061 := derived1061 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c1031 := derived1031 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c876 := derived876 a h
  have h8 : Entails.eval a c1015 := derived1015 a h
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c1037 := derived1037 a h
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  have h15 : Entails.eval a c442 := derived442 a h
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c928 := derived928 a h
  have h19 : Entails.eval a c1062 := derived1062 a h
  have h20 : Entails.eval a c1063 := derived1063 a h
  have h21 : Entails.eval a c10 := h 9 (by decide)
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c359 := h 358 (by decide)
  have h24 : Entails.eval a c353 := h 352 (by decide)
  have h25 : Entails.eval a c161 := h 160 (by decide)
  have h26 : Entails.eval a c274 := h 273 (by decide)
  have h27 : Entails.eval a c4 := h 3 (by decide)
  have h28 : Entails.eval a c320 := h 319 (by decide)
  have h29 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1065 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c782, some c1057, some c265, some c267, some c274, some c139, some c320, some c202, some c158, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1065 : lratChecker f1065 p1065 = .success := by decide +kernel
theorem unsat1065 : Unsatisfiable (PosFin 57) f1065 := by
  apply lratCheckerSound f1065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1065
  · intro a ha; simp [p1065] at ha; subst a; trivial
  · exact checked1065
theorem derived1065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1065 := by
  apply localUnsat_implies_entails f1065 [c782, c1057, c265, c267, c274, c139, c320, c202, c158] c1065 unsat1065 (by rfl) a
  have h0 : Entails.eval a c782 := derived782 a h
  have h1 : Entails.eval a c1057 := derived1057 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1066 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c359, some c1061, some c1048, some c1031, some c108, some c32, some c268, some c269, some c442, some c230, some c1010, some c870, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1066 : lratChecker f1066 p1066 = .success := by decide +kernel
theorem unsat1066 : Unsatisfiable (PosFin 57) f1066 := by
  apply lratCheckerSound f1066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1066
  · intro a ha; simp [p1066] at ha; subst a; trivial
  · exact checked1066
theorem derived1066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1066 := by
  apply localUnsat_implies_entails f1066 [c930, c997, c876, c1015, c359, c1061, c1048, c1031, c108, c32, c268, c269, c442, c230, c1010, c870] c1066 unsat1066 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c1061 := derived1061 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c1031 := derived1031 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c442 := derived442 a h
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c1010 := derived1010 a h
  have h15 : Entails.eval a c870 := derived870 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1067 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c1031, some c5, some c165, some c1064, some c930, some c876, some c1015, some c164, some c359, some c353, some c161, some c782, some c1066, some c265, some c267, some c1065, some c139, some c160, some c202, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1067 : lratChecker f1067 p1067 = .success := by decide +kernel
theorem unsat1067 : Unsatisfiable (PosFin 57) f1067 := by
  apply lratCheckerSound f1067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1067
  · intro a ha; simp [p1067] at ha; subst a; trivial
  · exact checked1067
theorem derived1067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1067 := by
  apply localUnsat_implies_entails f1067 [c997, c1031, c5, c165, c1064, c930, c876, c1015, c164, c359, c353, c161, c782, c1066, c265, c267, c1065, c139, c160, c202] c1067 unsat1067 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c1064 := derived1064 a h
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c876 := derived876 a h
  have h7 : Entails.eval a c1015 := derived1015 a h
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c782 := derived782 a h
  have h13 : Entails.eval a c1066 := derived1066 a h
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c1065 := derived1065 a h
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1068 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨12, by decide⟩, true), (⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c64, some c160, some c214, some c110, some c2, some c136, some c33, some c631, some c267, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1068 : lratChecker f1068 p1068 = .success := by decide +kernel
theorem unsat1068 : Unsatisfiable (PosFin 57) f1068 := by
  apply lratCheckerSound f1068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1068
  · intro a ha; simp [p1068] at ha; subst a; trivial
  · exact checked1068
theorem derived1068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1068 := by
  apply localUnsat_implies_entails f1068 [c60, c64, c160, c214, c110, c2, c136, c33, c631, c267] c1068 unsat1068 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c631 := derived631 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1069 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1005, some c265, some c267, some c269, some c34, some c35, some c110, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1069 : lratChecker f1069 p1069 = .success := by decide +kernel
theorem unsat1069 : Unsatisfiable (PosFin 57) f1069 := by
  apply lratCheckerSound f1069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1069
  · intro a ha; simp [p1069] at ha; subst a; trivial
  · exact checked1069
theorem derived1069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1069 := by
  apply localUnsat_implies_entails f1069 [c1005, c265, c267, c269, c34, c35, c110] c1069 unsat1069 (by rfl) a
  have h0 : Entails.eval a c1005 := derived1005 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1070 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1015, some c797, some c359, some c353, some c1069, some c1007, some c1000, some c268, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1070 : lratChecker f1070 p1070 = .success := by decide +kernel
theorem unsat1070 : Unsatisfiable (PosFin 57) f1070 := by
  apply lratCheckerSound f1070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1070
  · intro a ha; simp [p1070] at ha; subst a; trivial
  · exact checked1070
theorem derived1070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1070 := by
  apply localUnsat_implies_entails f1070 [c108, c1015, c797, c359, c353, c1069, c1007, c1000, c268] c1070 unsat1070 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1015 := derived1015 a h
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c353 := h 352 (by decide)
  have h5 : Entails.eval a c1069 := derived1069 a h
  have h6 : Entails.eval a c1007 := derived1007 a h
  have h7 : Entails.eval a c1000 := derived1000 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1071 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1061, some c1048, some c997, some c1031, some c5, some c108, some c876, some c930, some c165, some c1064, some c1067, some c10, some c207, some c1068, some c1070, some c32, some c870, some c269, some c442, some c140, some c36, some c61, some c2, some c315, some c151, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1071 : lratChecker f1071 p1071 = .success := by decide +kernel
theorem unsat1071 : Unsatisfiable (PosFin 57) f1071 := by
  apply lratCheckerSound f1071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1071
  · intro a ha; simp [p1071] at ha; subst a; trivial
  · exact checked1071
theorem derived1071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1071 := by
  apply localUnsat_implies_entails f1071 [c1061, c1048, c997, c1031, c5, c108, c876, c930, c165, c1064, c1067, c10, c207, c1068, c1070, c32, c870, c269, c442, c140, c36, c61, c2, c315, c151] c1071 unsat1071 (by rfl) a
  have h0 : Entails.eval a c1061 := derived1061 a h
  have h1 : Entails.eval a c1048 := derived1048 a h
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c1031 := derived1031 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c876 := derived876 a h
  have h7 : Entails.eval a c930 := derived930 a h
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c1064 := derived1064 a h
  have h10 : Entails.eval a c1067 := derived1067 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c1068 := derived1068 a h
  have h14 : Entails.eval a c1070 := derived1070 a h
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c870 := derived870 a h
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c442 := derived442 a h
  have h19 : Entails.eval a c140 := h 139 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c61 := h 60 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  have h23 : Entails.eval a c315 := h 314 (by decide)
  have h24 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1072 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c1031, some c5, some c1071, some c208, some c164, some c703, some c1066, some c353, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1072 : lratChecker f1072 p1072 = .success := by decide +kernel
theorem unsat1072 : Unsatisfiable (PosFin 57) f1072 := by
  apply lratCheckerSound f1072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1072
  · intro a ha; simp [p1072] at ha; subst a; trivial
  · exact checked1072
theorem derived1072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1072 := by
  apply localUnsat_implies_entails f1072 [c997, c1031, c5, c1071, c208, c164, c703, c1066, c353] c1072 unsat1072 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1071 := derived1071 a h
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c1066 := derived1066 a h
  have h8 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1073 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1072, some c930, some c997, some c876, some c1015, some c1031, some c5, some c1071, some c208, some c164, some c359, some c161, some c782, some c203, some c265, some c267, some c139, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1073 : lratChecker f1073 p1073 = .success := by decide +kernel
theorem unsat1073 : Unsatisfiable (PosFin 57) f1073 := by
  apply lratCheckerSound f1073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1073
  · intro a ha; simp [p1073] at ha; subst a; trivial
  · exact checked1073
theorem derived1073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1073 := by
  apply localUnsat_implies_entails f1073 [c1072, c930, c997, c876, c1015, c1031, c5, c1071, c208, c164, c359, c161, c782, c203, c265, c267, c139] c1073 unsat1073 (by rfl) a
  have h0 : Entails.eval a c1072 := derived1072 a h
  have h1 : Entails.eval a c930 := derived930 a h
  have h2 : Entails.eval a c997 := derived997 a h
  have h3 : Entails.eval a c876 := derived876 a h
  have h4 : Entails.eval a c1015 := derived1015 a h
  have h5 : Entails.eval a c1031 := derived1031 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1071 := derived1071 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c782 := derived782 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1074 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨39, by decide⟩, true), (⟨31, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c685, some c354, some c76, some c110, some c2, some c1037, some c146, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1074 : lratChecker f1074 p1074 = .success := by decide +kernel
theorem unsat1074 : Unsatisfiable (PosFin 57) f1074 := by
  apply lratCheckerSound f1074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1074
  · intro a ha; simp [p1074] at ha; subst a; trivial
  · exact checked1074
theorem derived1074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1074 := by
  apply localUnsat_implies_entails f1074 [c203, c685, c354, c76, c110, c2, c1037, c146] c1074 unsat1074 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c685 := derived685 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1037 := derived1037 a h
  have h7 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1075 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c24, some c268, some c269, some c354, some c230, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1075 : lratChecker f1075 p1075 = .success := by decide +kernel
theorem unsat1075 : Unsatisfiable (PosFin 57) f1075 := by
  apply lratCheckerSound f1075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1075
  · intro a ha; simp [p1075] at ha; subst a; trivial
  · exact checked1075
theorem derived1075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1075 := by
  apply localUnsat_implies_entails f1075 [c33, c24, c268, c269, c354, c230] c1075 unsat1075 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1076 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c108, some c631, some c265, some c267, some c125, some c532, some c332, some c173, some c81, some c1075, some c84, some c243, some c245, some c268, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1076 : lratChecker f1076 p1076 = .success := by decide +kernel
theorem unsat1076 : Unsatisfiable (PosFin 57) f1076 := by
  apply lratCheckerSound f1076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1076
  · intro a ha; simp [p1076] at ha; subst a; trivial
  · exact checked1076
theorem derived1076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1076 := by
  apply localUnsat_implies_entails f1076 [c359, c108, c631, c265, c267, c125, c532, c332, c173, c81, c1075, c84, c243, c245, c268] c1076 unsat1076 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c532 := derived532 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c1075 := derived1075 a h
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1077 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c930, some c997, some c876, some c1015, some c1031, some c108, some c5, some c1048, some c1061, some c1071, some c208, some c164, some c1072, some c1073, some c1076, some c353, some c702, some c1074, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1077 : lratChecker f1077 p1077 = .success := by decide +kernel
theorem unsat1077 : Unsatisfiable (PosFin 57) f1077 := by
  apply lratCheckerSound f1077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1077
  · intro a ha; simp [p1077] at ha; subst a; trivial
  · exact checked1077
theorem derived1077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1077 := by
  apply localUnsat_implies_entails f1077 [c930, c997, c876, c1015, c1031, c108, c5, c1048, c1061, c1071, c208, c164, c1072, c1073, c1076, c353, c702, c1074] c1077 unsat1077 (by rfl) a
  have h0 : Entails.eval a c930 := derived930 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c876 := derived876 a h
  have h3 : Entails.eval a c1015 := derived1015 a h
  have h4 : Entails.eval a c1031 := derived1031 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1048 := derived1048 a h
  have h8 : Entails.eval a c1061 := derived1061 a h
  have h9 : Entails.eval a c1071 := derived1071 a h
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c1072 := derived1072 a h
  have h13 : Entails.eval a c1073 := derived1073 a h
  have h14 : Entails.eval a c1076 := derived1076 a h
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c702 := derived702 a h
  have h17 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1078 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨18, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c19, some c39, some c213, some c219, some c277, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1078 : lratChecker f1078 p1078 = .success := by decide +kernel
theorem unsat1078 : Unsatisfiable (PosFin 57) f1078 := by
  apply lratCheckerSound f1078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1078
  · intro a ha; simp [p1078] at ha; subst a; trivial
  · exact checked1078
theorem derived1078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1078 := by
  apply localUnsat_implies_entails f1078 [c1077, c19, c39, c213, c219, c277] c1078 unsat1078 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1079 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c1077, some c1078, some c359, some c40, some c20, some c666, some c268, some c269, some c30, some c906, some c110, some c354, some c73, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1079 : lratChecker f1079 p1079 = .success := by decide +kernel
theorem unsat1079 : Unsatisfiable (PosFin 57) f1079 := by
  apply lratCheckerSound f1079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1079
  · intro a ha; simp [p1079] at ha; subst a; trivial
  · exact checked1079
theorem derived1079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1079 := by
  apply localUnsat_implies_entails f1079 [c353, c1077, c1078, c359, c40, c20, c666, c268, c269, c30, c906, c110, c354, c73] c1079 unsat1079 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1078 := derived1078 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c906 := derived906 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1080 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c26, some c3, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1080 : lratChecker f1080 p1080 = .success := by decide +kernel
theorem unsat1080 : Unsatisfiable (PosFin 57) f1080 := by
  apply lratCheckerSound f1080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1080
  · intro a ha; simp [p1080] at ha; subst a; trivial
  · exact checked1080
theorem derived1080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1080 := by
  apply localUnsat_implies_entails f1080 [c631, c26, c3] c1080 unsat1080 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1081 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1080, some c265, some c267, some c31, some c139, some c8, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1081 : lratChecker f1081 p1081 = .success := by decide +kernel
theorem unsat1081 : Unsatisfiable (PosFin 57) f1081 := by
  apply lratCheckerSound f1081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1081
  · intro a ha; simp [p1081] at ha; subst a; trivial
  · exact checked1081
theorem derived1081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1081 := by
  apply localUnsat_implies_entails f1081 [c1080, c265, c267, c31, c139, c8] c1081 unsat1081 (by rfl) a
  have h0 : Entails.eval a c1080 := derived1080 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1082 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨10, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c40, some c20, some c72, some c168, some c602, some c208, some c1081, some c271, some c734, some c267, some c139, some c793, some c206, some c138, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1082 : lratChecker f1082 p1082 = .success := by decide +kernel
theorem unsat1082 : Unsatisfiable (PosFin 57) f1082 := by
  apply lratCheckerSound f1082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1082
  · intro a ha; simp [p1082] at ha; subst a; trivial
  · exact checked1082
theorem derived1082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1082 := by
  apply localUnsat_implies_entails f1082 [c204, c40, c20, c72, c168, c602, c208, c1081, c271, c734, c267, c139, c793, c206, c138] c1082 unsat1082 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c602 := derived602 a h
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c1081 := derived1081 a h
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c734 := derived734 a h
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c793 := derived793 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1083 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c353, some c1079, some c114, some c204, some c1082, some c359, some c19, some c39, some c272, some c219, some c147, some c208, some c734, some c125, some c532, some c267, some c332, some c139, some c175, some c203, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1083 : lratChecker f1083 p1083 = .success := by decide +kernel
theorem unsat1083 : Unsatisfiable (PosFin 57) f1083 := by
  apply lratCheckerSound f1083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1083
  · intro a ha; simp [p1083] at ha; subst a; trivial
  · exact checked1083
theorem derived1083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1083 := by
  apply localUnsat_implies_entails f1083 [c1077, c353, c1079, c114, c204, c1082, c359, c19, c39, c272, c219, c147, c208, c734, c125, c532, c267, c332, c139, c175, c203] c1083 unsat1083 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1079 := derived1079 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c1082 := derived1082 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c532 := derived532 a h
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c175 := h 174 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1083

end CochromaticTwenty.Certificates.B16_4_2
