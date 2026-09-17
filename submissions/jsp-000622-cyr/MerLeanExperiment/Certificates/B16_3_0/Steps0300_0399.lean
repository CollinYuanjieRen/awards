import MerLeanExperiment.Certificates.B16_3_0.Steps0200_0299

/-! Generated from the actual pinned b16_3_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c672 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c651, some c655, some c25, some c636, some c660, some c671, some c304, some c58, some c156, some c668, some c663, some c34, some c153, some c272, some c126, some c255, some c258, some c198, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c651, c655, c25, c636, c660, c671, c304, c58, c156, c668, c663, c34, c153, c272, c126, c255, c258, c198] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c651 := derived651 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c636 := derived636 a h
  have h4 : Entails.eval a c660 := derived660 a h
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c668 := derived668 a h
  have h10 : Entails.eval a c663 := derived663 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c255 := h 254 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c651, some c636, some c655, some c25, some c637, some c259, some c672, some c301, some c302, some c645, some c271, some c153, some c667, some c662, some c34, some c59, some c125, some c308, some c255, some c201, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c651, c636, c655, c25, c637, c259, c672, c301, c302, c645, c271, c153, c667, c662, c34, c59, c125, c308, c255, c201] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c651 := derived651 a h
  have h1 : Entails.eval a c636 := derived636 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c672 := derived672 a h
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c645 := derived645 a h
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c667 := derived667 a h
  have h13 : Entails.eval a c662 := derived662 a h
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c308 := h 307 (by decide)
  have h18 : Entails.eval a c255 := h 254 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c651, some c673, some c253, some c254, some c648, some c20, some c139, some c668, some c666, some c302, some c663, some c41, some c136, some c250, some c198, some c303, some c143, some c217, some c208, some c70, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c636, c651, c673, c253, c254, c648, c20, c139, c668, c666, c302, c663, c41, c136, c250, c198, c303, c143, c217, c208, c70] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c651 := derived651 a h
  have h2 : Entails.eval a c673 := derived673 a h
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c254 := h 253 (by decide)
  have h5 : Entails.eval a c648 := derived648 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c668 := derived668 a h
  have h9 : Entails.eval a c666 := derived666 a h
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c663 := derived663 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c250 := h 249 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c303 := h 302 (by decide)
  have h17 : Entails.eval a c143 := h 142 (by decide)
  have h18 : Entails.eval a c217 := h 216 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c250, some c251, some c136, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c250, c251, c136] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c250 := h 249 (by decide)
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c636, some c675, some c18, some c199, some c667, some c305, some c304, some c59, some c198, some c153, some c252, some c126, some c272, some c281, some c89, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c674, c636, c675, c18, c199, c667, c305, c304, c59, c198, c153, c252, c126, c272, c281, c89] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c636 := derived636 a h
  have h2 : Entails.eval a c675 := derived675 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c117, some c662, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c18, c117, c662] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c662 := derived662 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c677, some c251, some c667, some c662, some c41, some c142, some c207, some c215, some c70, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c677, c251, c667, c662, c41, c142, c207, c215, c70] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c662 := derived662 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c676, some c677, some c251, some c20, some c28, some c637, some c80, some c290, some c235, some c64, some c678, some c44, some c81, some c317, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c636, c676, c677, c251, c20, c28, c637, c80, c290, c235, c64, c678, c44, c81, c317] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c676 := derived676 a h
  have h2 : Entails.eval a c677 := derived677 a h
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c678 := derived678 a h
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c679, some c665, some c666, some c18, some c53, some c250, some c305, some c303, some c202, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c674, c679, c665, c666, c18, c53, c250, c305, c303, c202] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c679 := derived679 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c666 := derived666 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c250 := h 249 (by decide)
  have h7 : Entails.eval a c305 := h 304 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c302, some c20, some c251, some c301, some c674, some c665, some c666, some c58, some c35, some c305, some c252, some c202, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c636, c302, c20, c251, c301, c674, c665, c666, c58, c35, c305, c252, c202] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c674 := derived674 a h
  have h6 : Entails.eval a c665 := derived665 a h
  have h7 : Entails.eval a c666 := derived666 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c62, some c317, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c26, c62, c317] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c680, some c301, some c302, some c20, some c46, some c153, some c251, some c209, some c681, some c61, some c237, some c288, some c83, some c682, some c667, some c662, some c59, some c125, some c279, some c271, some c89, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c636, c680, c301, c302, c20, c46, c153, c251, c209, c681, c61, c237, c288, c83, c682, c667, c662, c59, c125, c279, c271, c89] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c680 := derived680 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c681 := derived681 a h
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  have h12 : Entails.eval a c288 := h 287 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c682 := derived682 a h
  have h15 : Entails.eval a c667 := derived667 a h
  have h16 : Entails.eval a c662 := derived662 a h
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c125 := h 124 (by decide)
  have h19 : Entails.eval a c279 := h 278 (by decide)
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c302, some c636, some c59, some c271, some c279, some c89, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c302, c636, c59, c271, c279, c89] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c302 := h 301 (by decide)
  have h1 : Entails.eval a c636 := derived636 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c279 := h 278 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c674, some c636, some c302, some c681, some c20, some c46, some c251, some c209, some c61, some c237, some c288, some c83, some c682, some c667, some c684, some c227, some c125, some c357, some c363, some c192, some c187, some c167, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c683, c674, c636, c302, c681, c20, c46, c251, c209, c61, c237, c288, c83, c682, c667, c684, c227, c125, c357, c363, c192, c187, c167] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c674 := derived674 a h
  have h2 : Entails.eval a c636 := derived636 a h
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c681 := derived681 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c288 := h 287 (by decide)
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c682 := derived682 a h
  have h14 : Entails.eval a c667 := derived667 a h
  have h15 : Entails.eval a c684 := derived684 a h
  have h16 : Entails.eval a c227 := h 226 (by decide)
  have h17 : Entails.eval a c125 := h 124 (by decide)
  have h18 : Entails.eval a c357 := h 356 (by decide)
  have h19 : Entails.eval a c363 := h 362 (by decide)
  have h20 : Entails.eval a c192 := h 191 (by decide)
  have h21 : Entails.eval a c187 := h 186 (by decide)
  have h22 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c685, some c665, some c678, some c667, some c683, some c674, some c250, some c251, some c138, some c41, some c195, some c257, some c137, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c636, c685, c665, c678, c667, c683, c674, c250, c251, c138, c41, c195, c257, c137] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c685 := derived685 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c678 := derived678 a h
  have h4 : Entails.eval a c667 := derived667 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c674 := derived674 a h
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c685, some c683, some c674, some c636, some c665, some c667, some c678, some c686, some c117, some c199, some c192, some c305, some c304, some c198, some c20, some c46, some c252, some c209, some c118, some c137, some c531, some c218, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c685, c683, c674, c636, c665, c667, c678, c686, c117, c199, c192, c305, c304, c198, c20, c46, c252, c209, c118, c137, c531, c218] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c685 := derived685 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c674 := derived674 a h
  have h3 : Entails.eval a c636 := derived636 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c678 := derived678 a h
  have h7 : Entails.eval a c686 := derived686 a h
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c118 := h 117 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c531 := derived531 a h
  have h21 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c636, some c683, some c685, some c687, some c44, some c18, some c207, some c251, some c20, some c28, some c637, some c304, some c122, some c195, some c189, some c158, some c167, some c214, some c282, some c120, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c674, c636, c683, c685, c687, c44, c18, c207, c251, c20, c28, c637, c304, c122, c195, c189, c158, c167, c214, c282, c120] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c636 := derived636 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c685 := derived685 a h
  have h4 : Entails.eval a c687 := derived687 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c637 := derived637 a h
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c214 := h 213 (by decide)
  have h19 : Entails.eval a c282 := h 281 (by decide)
  have h20 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c655, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c649, c655] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c688, some c637, some c25, some c689, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c688, c637, c25, c689] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c688 := derived688 a h
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c689 := derived689 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨31, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c122, some c23, some c688, some c655, some c5, some c195, some c132, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c674, c122, c23, c688, c655, c5, c195, c132] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c688 := derived688 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c256, some c688, some c674, some c636, some c23, some c122, some c691, some c25, some c33, some c645, some c14, some c44, some c132, some c213, some c189, some c190, some c144, some c64, some c165, some c273, some c290, some c173, some c61, some c314, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c690, c256, c688, c674, c636, c23, c122, c691, c25, c33, c645, c14, c44, c132, c213, c189, c190, c144, c64, c165, c273, c290, c173, c61, c314] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c688 := derived688 a h
  have h3 : Entails.eval a c674 := derived674 a h
  have h4 : Entails.eval a c636 := derived636 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c691 := derived691 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c645 := derived645 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c273 := h 272 (by decide)
  have h21 : Entails.eval a c290 := h 289 (by decide)
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c61 := h 60 (by decide)
  have h24 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c688, some c636, some c692, some c305, some c304, some c46, some c58, some c213, some c666, some c44, some c25, some c645, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c690, c688, c636, c692, c305, c304, c46, c58, c213, c666, c44, c25, c645] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c688 := derived688 a h
  have h2 : Entails.eval a c636 := derived636 a h
  have h3 : Entails.eval a c692 := derived692 a h
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c666 := derived666 a h
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c645 := derived645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c688, some c693, some c665, some c25, some c600, some c690, some c256, some c33, some c636, some c305, some c304, some c275, some c58, some c130, some c15, some c14, some c156, some c132, some c189, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c674, c688, c693, c665, c25, c600, c690, c256, c33, c636, c305, c304, c275, c58, c130, c15, c14, c156, c132, c189] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c688 := derived688 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c600 := derived600 a h
  have h6 : Entails.eval a c690 := derived690 a h
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c636 := derived636 a h
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c132 := h 131 (by decide)
  have h19 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c688, some c674, some c256, some c693, some c665, some c667, some c25, some c33, some c34, some c600, some c255, some c694, some c122, some c202, some c14, some c303, some c301, some c132, some c137, some c190, some c662, some c151, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c690, c688, c674, c256, c693, c665, c667, c25, c33, c34, c600, c255, c694, c122, c202, c14, c303, c301, c132, c137, c190, c662, c151] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c688 := derived688 a h
  have h2 : Entails.eval a c674 := derived674 a h
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c693 := derived693 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c600 := derived600 a h
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c694 := derived694 a h
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c303 := h 302 (by decide)
  have h17 : Entails.eval a c301 := h 300 (by decide)
  have h18 : Entails.eval a c132 := h 131 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c190 := h 189 (by decide)
  have h21 : Entails.eval a c662 := derived662 a h
  have h22 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨31, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c695, some c199, some c301, some c202, some c688, some c644, some c271, some c665, some c667, some c227, some c34, some c358, some c258, some c226, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c674, c695, c199, c301, c202, c688, c644, c271, c665, c667, c227, c34, c358, c258, c226] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c695 := derived695 a h
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c688 := derived688 a h
  have h6 : Entails.eval a c644 := derived644 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c665 := derived665 a h
  have h9 : Entails.eval a c667 := derived667 a h
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c258 := h 257 (by decide)
  have h14 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c688, some c674, some c23, some c122, some c696, some c25, some c124, some c5, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c688, c674, c23, c122, c696, c25, c124, c5] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c688 := derived688 a h
  have h1 : Entails.eval a c674 := derived674 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c696 := derived696 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c674, some c688, some c695, some c697, some c305, some c304, some c58, some c668, some c666, some c34, some c25, some c275, some c227, some c271, some c354, some c198, some c230, some c258, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c636, c674, c688, c695, c697, c305, c304, c58, c668, c666, c34, c25, c275, c227, c271, c354, c198, c230, c258] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c674 := derived674 a h
  have h2 : Entails.eval a c688 := derived688 a h
  have h3 : Entails.eval a c695 := derived695 a h
  have h4 : Entails.eval a c697 := derived697 a h
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c668 := derived668 a h
  have h9 : Entails.eval a c666 := derived666 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c230 := h 229 (by decide)
  have h18 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨41, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c116, some c661, some c666, some c665, some c357, some c358, some c95, some c90, some c3, some c354, some c171, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c698, c17, c116, c661, c666, c665, c357, c358, c95, c90, c3, c354, c171] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c354, some c356, some c90, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c666, c665, c354, c356, c90] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c116, some c661, some c665, some c699, some c700, some c172, some c5, some c189, some c91, some c171, some c355, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c698, c17, c116, c661, c665, c699, c700, c172, c5, c189, c91, c171, c355] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c699 := derived699 a h
  have h6 : Entails.eval a c700 := derived700 a h
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c360, some c398, some c224, some c246, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c701, c360, c398, c224, c246] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c398 := derived398 a h
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨15, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c116, some c189, some c17, some c5, some c665, some c31, some c86, some c91, some c177, some c702, some c127, some c259, some c196, some c310, some c297, some c144, some c418, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c698, c116, c189, c17, c5, c665, c31, c86, c91, c177, c702, c127, c259, c196, c310, c297, c144, c418] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c177 := h 176 (by decide)
  have h10 : Entails.eval a c702 := derived702 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c259 := h 258 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c418 := derived418 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c703, some c116, some c190, some c189, some c17, some c661, some c666, some c665, some c171, some c173, some c286, some c53, some c48, some c276, some c320, some c143, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c698, c703, c116, c190, c189, c17, c661, c666, c665, c171, c173, c286, c53, c48, c276, c320, c143] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c661 := derived661 a h
  have h7 : Entails.eval a c666 := derived666 a h
  have h8 : Entails.eval a c665 := derived665 a h
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c276 := h 275 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨15, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c703, some c116, some c189, some c17, some c5, some c701, some c665, some c704, some c360, some c283, some c224, some c119, some c259, some c256, some c36, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c698, c703, c116, c189, c17, c5, c701, c665, c704, c360, c283, c224, c119, c259, c256, c36] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c701 := derived701 a h
  have h7 : Entails.eval a c665 := derived665 a h
  have h8 : Entails.eval a c704 := derived704 a h
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c666, some c665, some c116, some c189, some c190, some c703, some c705, some c26, some c90, some c286, some c53, some c156, some c307, some c283, some c196, some c127, some c256, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c698, c17, c666, c665, c116, c189, c190, c703, c705, c26, c90, c286, c53, c156, c307, c283, c196, c127, c256] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c703 := derived703 a h
  have h8 : Entails.eval a c705 := derived705 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c196 := h 195 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c706, some c17, some c116, some c661, some c666, some c286, some c22, some c48, some c325, some c164, some c216, some c320, some c126, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c698, c706, c17, c116, c661, c666, c286, c22, c48, c325, c164, c216, c320, c126] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c666, some c48, some c665, some c53, some c116, some c661, some c258, some c216, some c460, some c143, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c698, c17, c666, c48, c665, c53, c116, c661, c258, c216, c460, c143] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c661 := derived661 a h
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c460 := derived460 a h
  have h11 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨46, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c666, some c30, some c665, some c90, some c116, some c661, some c53, some c708, some c118, some c126, some c276, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c698, c17, c666, c30, c665, c90, c116, c661, c53, c708, c118, c126, c276] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c661 := derived661 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c708 := derived708 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c701, some c196, some c224, some c284, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c698, c701, c196, c224, c284] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨42, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c116, some c661, some c665, some c258, some c257, some c118, some c126, some c18, some c276, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c698, c17, c116, c661, c665, c258, c257, c118, c126, c18, c276] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c701, some c17, some c116, some c661, some c666, some c665, some c707, some c90, some c30, some c709, some c710, some c711, some c468, some c197, some c225, some c126, some c309, some c279, some c143, some c44, some c18, some c212, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c698, c701, c17, c116, c661, c666, c665, c707, c90, c30, c709, c710, c711, c468, c197, c225, c126, c309, c279, c143, c44, c18, c212] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c665 := derived665 a h
  have h7 : Entails.eval a c707 := derived707 a h
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c709 := derived709 a h
  have h11 : Entails.eval a c710 := derived710 a h
  have h12 : Entails.eval a c711 := derived711 a h
  have h13 : Entails.eval a c468 := derived468 a h
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c225 := h 224 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  have h17 : Entails.eval a c309 := h 308 (by decide)
  have h18 : Entails.eval a c279 := h 278 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c18 := h 17 (by decide)
  have h22 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨43, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c666, some c665, some c468, some c456, some c90, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c698, c17, c666, c665, c468, c456, c90] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c468 := derived468 a h
  have h5 : Entails.eval a c456 := derived456 a h
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨24, by decide⟩, false), (⟨43, by decide⟩, false), (⟨23, by decide⟩, false), (⟨47, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c90, some c30, some c85, some c359, some c248, some c249, some c353, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c666, c665, c90, c30, c85, c359, c248, c249, c353] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c276, some c280, some c53, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c666, c665, c276, c280, c53] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c712, some c706, some c130, some c116, some c661, some c172, some c713, some c714, some c666, some c665, some c715, some c143, some c316, some c320, some c71, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c698, c17, c712, c706, c130, c116, c661, c172, c713, c714, c666, c665, c715, c143, c316, c320, c71] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c706 := derived706 a h
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c661 := derived661 a h
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c713 := derived713 a h
  have h9 : Entails.eval a c714 := derived714 a h
  have h10 : Entails.eval a c666 := derived666 a h
  have h11 : Entails.eval a c665 := derived665 a h
  have h12 : Entails.eval a c715 := derived715 a h
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c701, some c17, some c116, some c661, some c665, some c706, some c712, some c130, some c172, some c713, some c714, some c362, some c716, some c81, some c26, some c170, some c243, some c175, some c345, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c698, c701, c17, c116, c661, c665, c706, c712, c130, c172, c713, c714, c362, c716, c81, c26, c170, c243, c175, c345] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c706 := derived706 a h
  have h7 : Entails.eval a c712 := derived712 a h
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c713 := derived713 a h
  have h11 : Entails.eval a c714 := derived714 a h
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c716 := derived716 a h
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c243 := h 242 (by decide)
  have h18 : Entails.eval a c175 := h 174 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c713, some c717, some c17, some c116, some c661, some c666, some c665, some c255, some c257, some c118, some c196, some c280, some c53, some c22, some c48, some c308, some c307, some c223, some c261, some c268, some c270, some c337, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c698, c713, c717, c17, c116, c661, c666, c665, c255, c257, c118, c196, c280, c53, c22, c48, c308, c307, c223, c261, c268, c270, c337] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c713 := derived713 a h
  have h2 : Entails.eval a c717 := derived717 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c661 := derived661 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c665 := derived665 a h
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c261 := h 260 (by decide)
  have h20 : Entails.eval a c268 := h 267 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  have h22 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c116, some c661, some c666, some c665, some c713, some c718, some c18, some c26, some c35, some c276, some c258, some c118, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c698, c17, c116, c661, c666, c665, c713, c718, c18, c26, c35, c276, c258, c118] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c713 := derived713 a h
  have h7 : Entails.eval a c718 := derived718 a h
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c276 := h 275 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c258, some c255, some c35, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c666, c665, c258, c255, c35] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c258 := h 257 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c701, some c17, some c116, some c661, some c666, some c719, some c126, some c720, some c197, some c225, some c287, some c22, some c708, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c698, c701, c17, c116, c661, c666, c719, c126, c720, c197, c225, c287, c22, c708] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c719 := derived719 a h
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c720 := derived720 a h
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c225 := h 224 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c708 := derived708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c721, some c709, some c17, some c666, some c665, some c90, some c717, some c701, some c116, some c197, some c225, some c309, some c279, some c654, some c54, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c698, c721, c709, c17, c666, c665, c90, c717, c701, c116, c197, c225, c309, c279, c654, c54] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c721 := derived721 a h
  have h2 : Entails.eval a c709 := derived709 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c701 := derived701 a h
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c225 := h 224 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c279 := h 278 (by decide)
  have h14 : Entails.eval a c654 := derived654 a h
  have h15 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c17, some c116, some c665, some c666, some c661, some c701, some c717, some c721, some c90, some c30, some c722, some c258, some c711, some c118, some c126, some c224, some c276, some c360, some c54, some c95, some c109, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c698, c17, c116, c665, c666, c661, c701, c717, c721, c90, c30, c722, c258, c711, c118, c126, c224, c276, c360, c54, c95, c109] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c661 := derived661 a h
  have h6 : Entails.eval a c701 := derived701 a h
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c721 := derived721 a h
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c722 := derived722 a h
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c711 := derived711 a h
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c276 := h 275 (by decide)
  have h18 : Entails.eval a c360 := h 359 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c95 := h 94 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c44, some c18, some c207, some c215, some c261, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c723, c698, c44, c18, c207, c215, c261] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c207, some c243, some c62, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c723, c207, c243, c62] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c666, some c665, some c661, some c141, some c150, some c664, some c87, some c725, some c35, some c210, some c249, some c66, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c698, c723, c666, c665, c661, c141, c150, c664, c87, c725, c35, c210, c249, c66] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c664 := derived664 a h
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c725 := derived725 a h
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c118, some c126, some c276, some c280, some c90, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c666, c665, c118, c126, c276, c280, c90] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c665, some c362, some c359, some c90, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c666, c665, c362, c359, c90] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c666, some c665, some c26, some c90, some c207, some c326, some c71, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c723, c666, c665, c26, c90, c207, c326, c71] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c666 := derived666 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c666, some c665, some c724, some c727, some c661, some c726, some c141, some c150, some c664, some c50, some c728, some c729, some c361, some c319, some c229, some c71, some c257, some c210, some c35, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c698, c723, c666, c665, c724, c727, c661, c726, c141, c150, c664, c50, c728, c729, c361, c319, c229, c71, c257, c210, c35] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c724 := derived724 a h
  have h5 : Entails.eval a c727 := derived727 a h
  have h6 : Entails.eval a c661 := derived661 a h
  have h7 : Entails.eval a c726 := derived726 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c664 := derived664 a h
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c728 := derived728 a h
  have h13 : Entails.eval a c729 := derived729 a h
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c71 := h 70 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c44, some c18, some c207, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c723, c44, c18, c207] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c666, some c665, some c730, some c309, some c118, some c661, some c141, some c731, some c308, some c201, some c257, some c35, some c254, some c210, some c36, some c71, some c109, some c335, some c76, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c698, c723, c666, c665, c730, c309, c118, c661, c141, c731, c308, c201, c257, c35, c254, c210, c36, c71, c109, c335, c76] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c730 := derived730 a h
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c661 := derived661 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c731 := derived731 a h
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c71 := h 70 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c335 := h 334 (by decide)
  have h20 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c665, some c666, some c732, some c53, some c22, some c48, some c210, some c223, some c141, some c261, some c661, some c306, some c118, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c723, c698, c665, c666, c732, c53, c22, c48, c210, c223, c141, c261, c661, c306, c118] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c665 := derived665 a h
  have h3 : Entails.eval a c666 := derived666 a h
  have h4 : Entails.eval a c732 := derived732 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c223 := h 222 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c661 := derived661 a h
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c188, some c186, some c134, some c254, some c210, some c135, some c160, some c189, some c335, some c165, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c723, c188, c186, c134, c254, c210, c135, c160, c189, c335, c165] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c188 := h 187 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c254 := h 253 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c335 := h 334 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c192, some c168, some c174, some c355, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c191, c192, c168, c174, c355] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c135, some c14, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c36, c135, c14] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c733, some c43, some c731, some c306, some c308, some c118, some c51, some c201, some c257, some c26, some c279, some c734, some c149, some c735, some c736, some c254, some c35, some c134, some c663, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c698, c723, c733, c43, c731, c306, c308, c118, c51, c201, c257, c26, c279, c734, c149, c735, c736, c254, c35, c134, c663] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c731 := derived731 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c735 := derived735 a h
  have h16 : Entails.eval a c736 := derived736 a h
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c663 := derived663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c43, some c731, some c118, some c126, some c276, some c616, some c90, some c80, some c356, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c698, c723, c43, c731, c118, c126, c276, c616, c90, c80, c356] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c616 := derived616 a h
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c733, some c43, some c737, some c52, some c668, some c738, some c664, some c150, some c188, some c734, some c207, some c62, some c71, some c235, some c210, some c80, some c129, some c314, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c698, c723, c733, c43, c737, c52, c668, c738, c664, c150, c188, c734, c207, c62, c71, c235, c210, c80, c129, c314] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c737 := derived737 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c668 := derived668 a h
  have h7 : Entails.eval a c738 := derived738 a h
  have h8 : Entails.eval a c664 := derived664 a h
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c734 := derived734 a h
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c80 := h 79 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c48, some c66, some c287, some c300, some c87, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c314, c48, c66, c287, c300, c87] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c739, some c667, some c733, some c30, some c85, some c238, some c249, some c100, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c723, c739, c667, c733, c30, c85, c238, c249, c100] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c733 := derived733 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c238 := h 237 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c733, some c739, some c667, some c52, some c43, some c741, some c740, some c89, some c287, some c22, some c48, some c210, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c698, c723, c733, c739, c667, c52, c43, c741, c740, c89, c287, c22, c48, c210] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c667 := derived667 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c741 := derived741 a h
  have h8 : Entails.eval a c740 := derived740 a h
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c146, some c121, some c210, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c723, c146, c121, c210] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c743, some c287, some c129, some c169, some c210, some c279, some c160, some c117, some c207, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c723, c743, c287, c129, c169, c210, c279, c160, c117, c207] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c287 := h 286 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c279 := h 278 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c129, some c169, some c210, some c311, some c160, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c723, c129, c169, c210, c311, c160] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨14, by decide⟩, true), (⟨33, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c745, some c314, some c160, some c207, some c311, some c125, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c723, c745, c314, c160, c207, c311, c125] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c667, some c52, some c43, some c662, some c663, some c744, some c89, some c746, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c698, c667, c52, c43, c662, c663, c744, c89, c746] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c662 := derived662 a h
  have h5 : Entails.eval a c663 := derived663 a h
  have h6 : Entails.eval a c744 := derived744 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c746 := derived746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c117, some c142, some c207, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c723, c117, c142, c207] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c733, some c43, some c739, some c667, some c52, some c742, some c747, some c118, some c306, some c748, some c126, some c281, some c87, some c295, some c89, some c312, some c356, some c354, some c309, some c207, some c335, some c198, some c162, some c330, some c249, some c179, some c346, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c698, c723, c733, c43, c739, c667, c52, c742, c747, c118, c306, c748, c126, c281, c87, c295, c89, c312, c356, c354, c309, c207, c335, c198, c162, c330, c249, c179, c346] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c739 := derived739 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c742 := derived742 a h
  have h8 : Entails.eval a c747 := derived747 a h
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c748 := derived748 a h
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c354 := h 353 (by decide)
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c207 := h 206 (by decide)
  have h22 : Entails.eval a c335 := h 334 (by decide)
  have h23 : Entails.eval a c198 := h 197 (by decide)
  have h24 : Entails.eval a c162 := h 161 (by decide)
  have h25 : Entails.eval a c330 := h 329 (by decide)
  have h26 : Entails.eval a c249 := h 248 (by decide)
  have h27 : Entails.eval a c179 := h 178 (by decide)
  have h28 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c733, some c43, some c739, some c667, some c52, some c742, some c747, some c118, some c126, some c306, some c309, some c281, some c89, some c312, some c749, some c262, some c210, some c338, some c198, some c164, some c257, some c675, some c195, some c137, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c723, c698, c733, c43, c739, c667, c52, c742, c747, c118, c126, c306, c309, c281, c89, c312, c749, c262, c210, c338, c198, c164, c257, c675, c195, c137] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c739 := derived739 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c742 := derived742 a h
  have h8 : Entails.eval a c747 := derived747 a h
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c312 := h 311 (by decide)
  have h16 : Entails.eval a c749 := derived749 a h
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c198 := h 197 (by decide)
  have h21 : Entails.eval a c164 := h 163 (by decide)
  have h22 : Entails.eval a c257 := h 256 (by decide)
  have h23 : Entails.eval a c675 := derived675 a h
  have h24 : Entails.eval a c195 := h 194 (by decide)
  have h25 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨34, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c750, some c720, some c43, some c208, some c252, some c250, some c44, some c677, some c198, some c667, some c143, some c52, some c309, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c723, c698, c750, c720, c43, c208, c252, c250, c44, c677, c198, c667, c143, c52, c309] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c720 := derived720 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c677 := derived677 a h
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c667 := derived667 a h
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c252, some c250, some c667, some c668, some c35, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c723, c252, c250, c667, c668, c35] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c250 := h 249 (by decide)
  have h3 : Entails.eval a c667 := derived667 a h
  have h4 : Entails.eval a c668 := derived668 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨34, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c751, some c750, some c720, some c752, some c52, some c250, some c26, some c62, some c279, some c294, some c87, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c723, c698, c751, c750, c720, c752, c52, c250, c26, c62, c279, c294, c87] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c751 := derived751 a h
  have h3 : Entails.eval a c750 := derived750 a h
  have h4 : Entails.eval a c720 := derived720 a h
  have h5 : Entails.eval a c752 := derived752 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c294 := h 293 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c750, some c720, some c752, some c52, some c43, some c208, some c252, some c250, some c751, some c306, some c143, some c753, some c662, some c747, some c125, some c30, some c279, some c740, some c89, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c723, c698, c750, c720, c752, c52, c43, c208, c252, c250, c751, c306, c143, c753, c662, c747, c125, c30, c279, c740, c89] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c720 := derived720 a h
  have h4 : Entails.eval a c752 := derived752 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c751 := derived751 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c753 := derived753 a h
  have h14 : Entails.eval a c662 := derived662 a h
  have h15 : Entails.eval a c747 := derived747 a h
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c30 := h 29 (by decide)
  have h18 : Entails.eval a c279 := h 278 (by decide)
  have h19 : Entails.eval a c740 := derived740 a h
  have h20 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c750, some c720, some c43, some c754, some c335, some c752, some c52, some c208, some c306, some c308, some c51, some c265, some c112, some c341, some c77, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c723, c698, c750, c720, c43, c754, c335, c752, c52, c208, c306, c308, c51, c265, c112, c341, c77] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c720 := derived720 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c754 := derived754 a h
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c752 := derived752 a h
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c750, some c720, some c752, some c52, some c43, some c208, some c252, some c250, some c677, some c198, some c143, some c309, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c723, c698, c750, c720, c752, c52, c43, c208, c252, c250, c677, c198, c143, c309] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c720 := derived720 a h
  have h4 : Entails.eval a c752 := derived752 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c677 := derived677 a h
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c750, some c250, some c720, some c43, some c752, some c52, some c754, some c756, some c755, some c26, some c279, some c311, some c89, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c723, c698, c750, c250, c720, c43, c752, c52, c754, c756, c755, c26, c279, c311, c89] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c750 := derived750 a h
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c720 := derived720 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c752 := derived752 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c754 := derived754 a h
  have h9 : Entails.eval a c756 := derived756 a h
  have h10 : Entails.eval a c755 := derived755 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c311 := h 310 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c32, some c131, some c664, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c757, c32, c131, c664] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c664 := derived664 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨34, by decide⟩, true), (⟨56, by decide⟩, true), (⟨42, by decide⟩, true), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c616, some c71, some c90, some c326, some c287, some c328, some c22, some c210, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c723, c616, c71, c90, c326, c287, c328, c22, c210] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c616 := derived616 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c308, some c306, some c143, some c265, some c758, some c279, some c616, some c81, some c26, some c294, some c250, some c201, some c214, some c759, some c668, some c666, some c100, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c723, c308, c306, c143, c265, c758, c279, c616, c81, c26, c294, c250, c201, c214, c759, c668, c666, c100] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c758 := derived758 a h
  have h6 : Entails.eval a c279 := h 278 (by decide)
  have h7 : Entails.eval a c616 := derived616 a h
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c759 := derived759 a h
  have h15 : Entails.eval a c668 := derived668 a h
  have h16 : Entails.eval a c666 := derived666 a h
  have h17 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c68, some c666, some c342, some c339, some c71, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c100, c68, c666, c342, c339, c71] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c698, some c760, some c308, some c306, some c279, some c616, some c81, some c26, some c294, some c250, some c201, some c761, some c668, some c759, some c207, some c214, some c260, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c723, c698, c760, c308, c306, c279, c616, c81, c26, c294, c250, c201, c761, c668, c759, c207, c214, c260] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c760 := derived760 a h
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c279 := h 278 (by decide)
  have h6 : Entails.eval a c616 := derived616 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c761 := derived761 a h
  have h13 : Entails.eval a c668 := derived668 a h
  have h14 : Entails.eval a c759 := derived759 a h
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c306, some c762, some c32, some c758, some c752, some c118, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c757, c306, c762, c32, c758, c752, c118] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c758 := derived758 a h
  have h5 : Entails.eval a c752 := derived752 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c763, some c18, some c731, some c250, some c43, some c141, some c666, some c661, some c53, some c118, some c309, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c698, c723, c763, c18, c731, c250, c43, c141, c666, c661, c53, c118, c309] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c731 := derived731 a h
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c666 := derived666 a h
  have h9 : Entails.eval a c661 := derived661 a h
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c757, some c698, some c723, some c764, some c665, some c43, some c748, some c662, some c667, some c32, some c309, some c281, some c126, some c250, some c252, some c198, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c757, c698, c723, c764, c665, c43, c748, c662, c667, c32, c309, c281, c126, c250, c252, c198] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c757 := derived757 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c764 := derived764 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c748 := derived748 a h
  have h7 : Entails.eval a c662 := derived662 a h
  have h8 : Entails.eval a c667 := derived667 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c723, some c764, some c665, some c43, some c748, some c662, some c765, some c118, some c143, some c208, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c698, c723, c764, c665, c43, c748, c662, c765, c118, c143, c208] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c764 := derived764 a h
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c748 := derived748 a h
  have h6 : Entails.eval a c662 := derived662 a h
  have h7 : Entails.eval a c765 := derived765 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c757, some c723, some c764, some c665, some c667, some c32, some c766, some c306, some c308, some c279, some c51, some c112, some c41, some c251, some c125, some c662, some c8, some c154, some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c698, c757, c723, c764, c665, c667, c32, c766, c306, c308, c279, c51, c112, c41, c251, c125, c662, c8, c154] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c764 := derived764 a h
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c766 := derived766 a h
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c662 := derived662 a h
  have h17 : Entails.eval a c8 := h 7 (by decide)
  have h18 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c767, some c757, some c24, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c767, c757, c24] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c767 := derived767 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c767, some c757, some c123, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c767, c757, c123] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c767 := derived767 a h
  have h1 : Entails.eval a c757 := derived757 a h
  have h2 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c768, some c667, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c768, c667] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c768 := derived768 a h
  have h1 : Entails.eval a c667 := derived667 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c768, some c668, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c768, c668] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c768 := derived768 a h
  have h1 : Entails.eval a c668 := derived668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived771

end CochromaticTwenty.Certificates.B16_3_0
