import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c658 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c107, some c80, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p658 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 31) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c656, c107, c80] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c213, some c504, some c495, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p659 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 31) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c213, c504, c495] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c213 := h 212 (by decide)
  have h1 : Entails.eval a c504 := h 503 (by decide)
  have h2 : Entails.eval a c495 := h 494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c656, some c657, some c157, some c111, some c658, some c164, some c593, some c639, some c12, some c659, some c248, some c211, some c442, some c375, some c412, some c344, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p660 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 31) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c590, c656, c657, c157, c111, c658, c164, c593, c639, c12, c659, c248, c211, c442, c375, c412, c344] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c657 := derived657 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c658 := derived658 a h
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c593 := derived593 a h
  have h8 : Entails.eval a c639 := derived639 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c659 := derived659 a h
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c211 := h 210 (by decide)
  have h13 : Entails.eval a c442 := h 441 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c412 := h 411 (by decide)
  have h16 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c344, some c383, some c470, some c315, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p661 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 31) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c344, c383, c470, c315] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c470 := h 469 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c639, some c590, some c657, some c111, some c157, some c658, some c164, some c660, some c153, some c211, some c260, some c661, some c491, some c135, some c292, some c217, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p662 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 31) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c656, c639, c590, c657, c111, c157, c658, c164, c660, c153, c211, c260, c661, c491, c135, c292, c217] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c590 := derived590 a h
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c658 := derived658 a h
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c660 := derived660 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c661 := derived661 a h
  have h13 : Entails.eval a c491 := h 490 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c662, some c639, some c132, some c116, some c656, some c92, some c590, some c157, some c658, some c164, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p663 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 31) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c662, c639, c132, c116, c656, c92, c590, c157, c658, c164] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c662 := derived662 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c590 := derived590 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c658 := derived658 a h
  have h9 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c639, some c590, some c662, some c132, some c116, some c663, some c113, some c252, some c211, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p664 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 31) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c656, c639, c590, c662, c132, c116, c663, c113, c252, c211] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c590 := derived590 a h
  have h3 : Entails.eval a c662 := derived662 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c663 := derived663 a h
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c664, some c38, some c656, some c18, some c243, some c74, some c164, some c92, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p665 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 31) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c590, c664, c38, c656, c18, c243, c74, c164, c92] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c664 := derived664 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c656 := derived656 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c639, some c656, some c590, some c664, some c38, some c665, some c251, some c117, some c80, some c271, some c17, some c92, some c252, some c42, some c392, some c171, some c235, some c242, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p666 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 31) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c639, c656, c590, c664, c38, c665, c251, c117, c80, c271, c17, c92, c252, c42, c392, c171, c235, c242] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c639 := derived639 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c590 := derived590 a h
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c392 := h 391 (by decide)
  have h15 : Entails.eval a c171 := h 170 (by decide)
  have h16 : Entails.eval a c235 := h 234 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c590, some c664, some c38, some c665, some c251, some c639, some c92, some c117, some c80, some c271, some c17, some c666, some c97, some c341, some c173, some c285, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p667 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 31) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c656, c590, c664, c38, c665, c251, c639, c92, c117, c80, c271, c17, c666, c97, c341, c173, c285] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c664 := derived664 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c639 := derived639 a h
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c666 := derived666 a h
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c341 := h 340 (by decide)
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c161, some c243, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p668 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 31) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c161, c243] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c161 := h 160 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c669 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c664, some c656, some c639, some c590, some c38, some c665, some c251, some c668, some c74, some c271, some c667, some c17, some c202, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p669 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 31) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c664, c656, c639, c590, c38, c665, c251, c668, c74, c271, c667, c17, c202] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c664 := derived664 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c590 := derived590 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c668 := derived668 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c667 := derived667 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c669, some c157, some c664, some c590, some c92, some c126, some c164, some c175, some c243, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p670 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 31) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c656, c669, c157, c664, c590, c92, c126, c164, c175, c243] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c669 := derived669 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c590 := derived590 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c664, some c670, some c118, some c669, some c656, some c107, some c80, some c81, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p671 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 31) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c590, c664, c670, c118, c669, c656, c107, c80, c81] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c664 := derived664 a h
  have h2 : Entails.eval a c670 := derived670 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c656 := derived656 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c669, some c157, some c664, some c590, some c42, some c22, some c1, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p672 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 31) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c656, c669, c157, c664, c590, c42, c22, c1] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c669 := derived669 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c590 := derived590 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c656, some c669, some c157, some c671, some c164, some c664, some c670, some c118, some c672, some c68, some c95, some c395, some c40, some c294, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p673 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 31) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c590, c656, c669, c157, c671, c164, c664, c670, c118, c672, c68, c95, c395, c40, c294] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c672 := derived672 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c395 := h 394 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c590, some c669, some c157, some c671, some c164, some c664, some c670, some c673, some c212, some c248, some c118, some c68, some c95, some c146, some c180, some c294, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p674 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 31) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c656, c590, c669, c157, c671, c164, c664, c670, c673, c212, c248, c118, c68, c95, c146, c180, c294] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c673 := derived673 a h
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c656, some c669, some c157, some c671, some c164, some c664, some c670, some c118, some c673, some c212, some c248, some c674, some c42, some c22, some c138, some c218, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p675 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 31) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c590, c656, c669, c157, c671, c164, c664, c670, c118, c673, c212, c248, c674, c42, c22, c138, c218] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c673 := derived673 a h
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c674 := derived674 a h
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c675, some c590, some c656, some c669, some c157, some c671, some c164, some c664, some c670, some c118, some c639, some c420, some c524, some c364, some c261, some c102, some c323, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p676 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 31) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c675, c590, c656, c669, c157, c671, c164, c664, c670, c118, c639, c420, c524, c364, c261, c102, c323] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c675 := derived675 a h
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c656 := derived656 a h
  have h3 : Entails.eval a c669 := derived669 a h
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c664 := derived664 a h
  have h8 : Entails.eval a c670 := derived670 a h
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c639 := derived639 a h
  have h11 : Entails.eval a c420 := h 419 (by decide)
  have h12 : Entails.eval a c524 := h 523 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c656, some c669, some c157, some c671, some c164, some c664, some c670, some c118, some c675, some c621, some c648, some c676, some c441, some c547, some c51, some c106, some c290, some c295, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p677 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 31) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c590, c656, c669, c157, c671, c164, c664, c670, c118, c675, c621, c648, c676, c441, c547, c51, c106, c290, c295] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c656 := derived656 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c675 := derived675 a h
  have h10 : Entails.eval a c621 := derived621 a h
  have h11 : Entails.eval a c648 := derived648 a h
  have h12 : Entails.eval a c676 := derived676 a h
  have h13 : Entails.eval a c441 := h 440 (by decide)
  have h14 : Entails.eval a c547 := h 546 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c290 := h 289 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c677, some c671, some c656, some c669, some c157, some c664, some c621, some c260, some c210, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p678 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 31) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c677, c671, c656, c669, c157, c664, c621, c260, c210] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c656 := derived656 a h
  have h3 : Entails.eval a c669 := derived669 a h
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c664 := derived664 a h
  have h6 : Entails.eval a c621 := derived621 a h
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c678, some c677, some c590, some c656, some c669, some c157, some c671, some c164, some c664, some c670, some c118, some c672, some c655, some c68, some c95, some c40, some c35, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p679 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 31) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c678, c677, c590, c656, c669, c157, c671, c164, c664, c670, c118, c672, c655, c68, c95, c40, c35] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c678 := derived678 a h
  have h1 : Entails.eval a c677 := derived677 a h
  have h2 : Entails.eval a c590 := derived590 a h
  have h3 : Entails.eval a c656 := derived656 a h
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c671 := derived671 a h
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c664 := derived664 a h
  have h9 : Entails.eval a c670 := derived670 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c672 := derived672 a h
  have h12 : Entails.eval a c655 := derived655 a h
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c40 := h 39 (by decide)
  have h16 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c656, some c590, some c669, some c157, some c671, some c164, some c664, some c670, some c679, some c212, some c248, some c678, some c40, some c20, some c265, some c256, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p680 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 31) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c656, c590, c669, c157, c671, c164, c664, c670, c679, c212, c248, c678, c40, c20, c265, c256] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c679 := derived679 a h
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c678 := derived678 a h
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c590, some c639, some c656, some c664, some c669, some c157, some c670, some c118, some c671, some c164, some c677, some c678, some c679, some c212, some c248, some c211, some c680, some c68, some c462, some c497, some c42, some c313, some c30, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p681 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 31) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c590, c639, c656, c664, c669, c157, c670, c118, c671, c164, c677, c678, c679, c212, c248, c211, c680, c68, c462, c497, c42, c313, c30] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c656 := derived656 a h
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c670 := derived670 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c671 := derived671 a h
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c677 := derived677 a h
  have h11 : Entails.eval a c678 := derived678 a h
  have h12 : Entails.eval a c679 := derived679 a h
  have h13 : Entails.eval a c212 := h 211 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c680 := derived680 a h
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c462 := h 461 (by decide)
  have h19 : Entails.eval a c497 := h 496 (by decide)
  have h20 : Entails.eval a c42 := h 41 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c166, some c248, some c42, some c22, some c265, some c259, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p682 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 31) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c681, c166, c248, c42, c22, c265, c259] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c166, some c248, some c682, some c181, some c40, some c20, some c265, some c256, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p683 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 31) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c681, c166, c248, c682, c181, c40, c20, c265, c256] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c682 := derived682 a h
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c683, some c164, some c163, some c243, some c38, some c253, some c26, some c107, some c244, some c45, some c19, some c108, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p684 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 31) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c681, c683, c164, c163, c243, c38, c253, c26, c107, c244, c45, c19, c108] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c179, some c166, some c186, some c244, some c446, some c389, some c195, some c194, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p685 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 31) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c681, c179, c166, c186, c244, c446, c389, c195, c194] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c244 := h 243 (by decide)
  have h5 : Entails.eval a c446 := h 445 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c26, some c76, some c119, some c531, some c499, some c542, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p686 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 31) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c681, c26, c76, c119, c531, c499, c542] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c531 := h 530 (by decide)
  have h5 : Entails.eval a c499 := h 498 (by decide)
  have h6 : Entails.eval a c542 := h 541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c684, some c179, some c212, some c78, some c166, some c186, some c686, some c203, some c685, some c119, some c45, some c385, some c536, some c240, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p687 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 31) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c681, c684, c179, c212, c78, c166, c186, c686, c203, c685, c119, c45, c385, c536, c240] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c686 := derived686 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c685 := derived685 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c385 := h 384 (by decide)
  have h13 : Entails.eval a c536 := h 535 (by decide)
  have h14 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c684, some c179, some c166, some c186, some c212, some c78, some c687, some c630, some c115, some c119, some c114, some c37, some c244, some c446, some c549, some c239, some c483, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p688 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 31) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c681, c684, c179, c166, c186, c212, c78, c687, c630, c115, c119, c114, c37, c244, c446, c549, c239, c483] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c687 := derived687 a h
  have h8 : Entails.eval a c630 := derived630 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c244 := h 243 (by decide)
  have h14 : Entails.eval a c446 := h 445 (by decide)
  have h15 : Entails.eval a c549 := h 548 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c483 := h 482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c684, some c179, some c186, some c166, some c688, some c243, some c96, some c655, some c210, some c119, some c555, some c78, some c509, some c15, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p689 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 31) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c681, c684, c179, c186, c166, c688, c243, c96, c655, c210, c119, c555, c78, c509, c15] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c688 := derived688 a h
  have h6 : Entails.eval a c243 := h 242 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c655 := derived655 a h
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c555 := h 554 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c509 := h 508 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c351, some c336, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p690 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 31) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c681, c351, c336] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c351 := h 350 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨28, by decide⟩, false), (⟨7, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c393, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p691 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 31) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c681, c73, c393] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c96, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p692 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 31) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c88, c96] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c693 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c690, some c691, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p693 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 31) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c690, c691] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c691 := derived691 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c694 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c397, some c69, some c556, some c21, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p694 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 31) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c681, c73, c397, c69, c556, c21] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c397 := h 396 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c556 := h 555 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c262, some c165, some c692, some c73, some c272, some c693, some c212, some c114, some c694, some c43, some c23, some c3, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p695 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 31) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c681, c262, c165, c692, c73, c272, c693, c212, c114, c694, c43, c23, c3] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c692 := derived692 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c693 := derived693 a h
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c694 := derived694 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c689, some c262, some c165, some c692, some c73, some c695, some c655, some c211, some c212, some c114, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p696 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 31) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c681, c689, c262, c165, c692, c73, c695, c655, c211, c212, c114] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c689 := derived689 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c692 := derived692 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c695 := derived695 a h
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c114, some c119, some c211, some c356, some c411, some c398, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p697 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 31) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c681, c73, c114, c119, c211, c356, c411, c398] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c411 := h 410 (by decide)
  have h7 : Entails.eval a c398 := h 397 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c697, some c115, some c76, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p698 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 31) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c697, c115, c76] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c697 := derived697 a h
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c165, some c272, some c212, some c698, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p699 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 31) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c681, c165, c272, c212, c698] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c698 := derived698 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c210, some c691, some c430, some c43, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p700 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 31) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c681, c73, c210, c691, c430, c43] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c430 := h 429 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c689, some c262, some c165, some c272, some c696, some c699, some c700, some c88, some c129, some c413, some c396, some c32, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p701 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 31) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c681, c689, c262, c165, c272, c696, c699, c700, c88, c129, c413, c396, c32] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c689 := derived689 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c696 := derived696 a h
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c700 := derived700 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c413 := h 412 (by decide)
  have h11 : Entails.eval a c396 := h 395 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c701, some c689, some c262, some c165, some c163, some c164, some c272, some c700, some c202, some c610, some c118, some c74, some c514, some c463, some c464, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p702 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 31) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c681, c701, c689, c262, c165, c163, c164, c272, c700, c202, c610, c118, c74, c514, c463, c464] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c700 := derived700 a h
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c610 := derived610 a h
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c514 := h 513 (by decide)
  have h14 : Entails.eval a c463 := h 462 (by decide)
  have h15 : Entails.eval a c464 := h 463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c689, some c262, some c165, some c701, some c163, some c164, some c702, some c38, some c212, some c117, some c76, some c119, some c73, some c352, some c381, some c22, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p703 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 31) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c681, c689, c262, c165, c701, c163, c164, c702, c38, c212, c117, c76, c119, c73, c352, c381, c22] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c689 := derived689 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c702 := derived702 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c249, some c211, some c119, some c536, some c465, some c470, some c482, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p704 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 31) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c681, c703, c249, c211, c119, c536, c465, c470, c482] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c536 := h 535 (by decide)
  have h6 : Entails.eval a c465 := h 464 (by decide)
  have h7 : Entails.eval a c470 := h 469 (by decide)
  have h8 : Entails.eval a c482 := h 481 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c703, some c591, some c249, some c704, some c429, some c533, some c50, some c32, some c295, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p705 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 31) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c681, c73, c703, c591, c249, c704, c429, c533, c50, c32, c295] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c703 := derived703 a h
  have h3 : Entails.eval a c591 := derived591 a h
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c704 := derived704 a h
  have h6 : Entails.eval a c429 := h 428 (by decide)
  have h7 : Entails.eval a c533 := h 532 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c705, some c165, some c530, some c427, some c247, some c41, some c20, some c22, some c43, some c5, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p706 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 31) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c681, c73, c705, c165, c530, c427, c247, c41, c20, c22, c43, c5] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c530 := h 529 (by decide)
  have h5 : Entails.eval a c427 := h 426 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c706, some c112, some c222, some c447, some c77, some c550, some c22, some c213, some c299, some c276, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p707 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 31) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c681, c703, c706, c112, c222, c447, c77, c550, c22, c213, c299, c276] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c706 := derived706 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c447 := h 446 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c550 := h 549 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c213 := h 212 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c112, some c222, some c447, some c77, some c550, some c23, some c213, some c299, some c276, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p708 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 31) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c681, c112, c222, c447, c77, c550, c23, c213, c299, c276] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c447 := h 446 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c550 := h 549 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c708, some c73, some c165, some c249, some c704, some c119, some c211, some c429, some c533, some c213, some c50, some c103, some c287, some c297, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p709 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 31) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c681, c703, c708, c73, c165, c249, c704, c119, c211, c429, c533, c213, c50, c103, c287, c297] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c708 := derived708 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c704 := derived704 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c429 := h 428 (by decide)
  have h10 : Entails.eval a c533 := h 532 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c287 := h 286 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some c160, some c75, some c114, some c119, some c50, some c263, some c145, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p710 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 31) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c681, c73, c160, c75, c114, c119, c50, c263, c145] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c707, some c708, some c73, some c709, some c160, some c75, some c114, some c119, some c211, some c710, some c55, some c99, some c133, some c48, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p711 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 31) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c681, c703, c707, c708, c73, c709, c160, c75, c114, c119, c211, c710, c55, c99, c133, c48] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c707 := derived707 a h
  have h3 : Entails.eval a c708 := derived708 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c709 := derived709 a h
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c710 := derived710 a h
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c711, some c700, some c112, some c222, some c447, some c165, some c23, some c405, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p712 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 31) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c681, c703, c711, c700, c112, c222, c447, c165, c23, c405] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c700 := derived700 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c447 := h 446 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c712, some c703, some c222, some c165, some c692, some c164, some c591, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p713 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 31) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c681, c712, c703, c222, c165, c692, c164, c591] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c703 := derived703 a h
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c692 := derived692 a h
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c164, some c591, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p714 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 31) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c164, c591] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c164 := h 163 (by decide)
  have h1 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c715 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c43, some c23, some c232, some c188, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p715 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 31) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c681, c43, c23, c232, c188] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c249, some c119, some c73, some c407, some c100, some c50, some c57, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p716 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 31) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c681, c249, c119, c73, c407, c100, c50, c57] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c407 := h 406 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c713, some c712, some c703, some c165, some c249, some c211, some c213, some c716, some c23, some c351, some c382, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p717 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 31) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c681, c713, c712, c703, c165, c249, c211, c213, c716, c23, c351, c382] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c713 := derived713 a h
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c703 := derived703 a h
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c716 := derived716 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c717, some c713, some c73, some c712, some c703, some c7, some c249, some c714, some c28, some c119, some c75, some c710, some c716, some c99, some c133, some c48, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p718 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 31) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c681, c717, c713, c73, c712, c703, c7, c249, c714, c28, c119, c75, c710, c716, c99, c133, c48] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c717 := derived717 a h
  have h2 : Entails.eval a c713 := derived713 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c703 := derived703 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c714 := derived714 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c710 := derived710 a h
  have h13 : Entails.eval a c716 := derived716 a h
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c712, some c713, some c73, some c717, some c718, some c46, some c247, some c211, some c254, some c164, some c75, some c710, some c99, some c100, some c289, some c264, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p719 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 31) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c681, c703, c712, c713, c73, c717, c718, c46, c247, c211, c254, c164, c75, c710, c99, c100, c289, c264] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c713 := derived713 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c717 := derived717 a h
  have h6 : Entails.eval a c718 := derived718 a h
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c710 := derived710 a h
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c100 := h 99 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c222, some c719, some c179, some c22, some c24, some c190, some c14, some c248, some c93, some c119, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p720 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 31) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c681, c703, c222, c719, c179, c22, c24, c190, c14, c248, c93, c119] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c719 := derived719 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c222, some c719, some c179, some c119, some c211, some c254, some c164, some c288, some c172, some c94, some c285, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p721 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 31) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c681, c703, c222, c719, c179, c119, c211, c254, c164, c288, c172, c94, c285] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c719 := derived719 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c703, some c222, some c719, some c179, some c720, some c721, some c210, some c248, some c26, some c164, some c254, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p722 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 31) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c703, c222, c719, c179, c720, c721, c210, c248, c26, c164, c254] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c703 := derived703 a h
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c720 := derived720 a h
  have h5 : Entails.eval a c721 := derived721 a h
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c719, some c703, some c179, some c222, some c722, some c249, some c714, some c119, some c721, some c170, some c93, some c14, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p723 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 31) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c681, c719, c703, c179, c222, c722, c249, c714, c119, c721, c170, c93, c14] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c719 := derived719 a h
  have h2 : Entails.eval a c703 := derived703 a h
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c722 := derived722 a h
  have h6 : Entails.eval a c249 := h 248 (by decide)
  have h7 : Entails.eval a c714 := derived714 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c721 := derived721 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c719, some c723, some c166, some c703, some c249, some c714, some c692, some c119, some c211, some c78, some c213, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p724 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 31) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c681, c719, c723, c166, c703, c249, c714, c692, c119, c211, c78, c213] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c719 := derived719 a h
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c703 := derived703 a h
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c714 := derived714 a h
  have h7 : Entails.eval a c692 := derived692 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c719, some c723, some c166, some c703, some c119, some c211, some c213, some c78, some c164, some c243, some c244, some c107, some c19, some c630, some c108, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p725 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 31) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c681, c719, c723, c166, c703, c119, c211, c213, c78, c164, c243, c244, c107, c19, c630, c108] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c719 := derived719 a h
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c703 := derived703 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c630 := derived630 a h
  have h15 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c19, some c209, some c154, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p726 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 31) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c681, c19, c209, c154] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c724, some c719, some c723, some c166, some c703, some c725, some c210, some c26, some c213, some c726, some c244, some c164, some c78, some c343, some c461, some c325, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p727 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 31) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c681, c724, c719, c723, c166, c703, c725, c210, c26, c213, c726, c244, c164, c78, c343, c461, c325] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c724 := derived724 a h
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c723 := derived723 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c703 := derived703 a h
  have h6 : Entails.eval a c725 := derived725 a h
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c213 := h 212 (by decide)
  have h10 : Entails.eval a c726 := derived726 a h
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c461 := h 460 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c727, some c112, some c724, some c719, some c723, some c166, some c36, some c154, some c213, some c47, some c26, some c243, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p728 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 31) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c681, c703, c727, c112, c724, c719, c723, c166, c36, c154, c213, c47, c26, c243] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c727 := derived727 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c724 := derived724 a h
  have h5 : Entails.eval a c719 := derived719 a h
  have h6 : Entails.eval a c723 := derived723 a h
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c703, some c719, some c723, some c166, some c724, some c727, some c112, some c728, some c120, some c496, some c543, some c190, some c69, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p729 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 31) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c681, c703, c719, c723, c166, c724, c727, c112, c728, c120, c496, c543, c190, c69] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c723 := derived723 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c724 := derived724 a h
  have h6 : Entails.eval a c727 := derived727 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c728 := derived728 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c496 := h 495 (by decide)
  have h11 : Entails.eval a c543 := h 542 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c120, some c496, some c382, some c21, some c23, some c69, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p730 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 31) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c681, c120, c496, c382, c21, c23, c69] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c496 := h 495 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c630, some c729, some c402, some c68, some c212, some c21, some c114, some c551, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p731 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 31) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c681, c630, c729, c402, c68, c212, c21, c114, c551] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c630 := derived630 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c402 := h 401 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c551 := h 550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c729, some c251, some c166, some c158, some c630, some c731, some c23, some c24, some c21, some c317, some c174, some c512, some c316, some c258, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p732 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 31) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c681, c729, c251, c166, c158, c630, c731, c23, c24, c21, c317, c174, c512, c316, c258] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c630 := derived630 a h
  have h6 : Entails.eval a c731 := derived731 a h
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c174 := h 173 (by decide)
  have h12 : Entails.eval a c512 := h 511 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c166, some c729, some c158, some c730, some c251, some c732, some c154, some c108, some c64, some c212, some c38, some c117, some c76, some c26, some c500, some c378, some c255, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p733 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 31) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c681, c166, c729, c158, c730, c251, c732, c154, c108, c64, c212, c38, c117, c76, c26, c500, c378, c255] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c730 := derived730 a h
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c732 := derived732 a h
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c500 := h 499 (by decide)
  have h16 : Entails.eval a c378 := h 377 (by decide)
  have h17 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c114, some c171, some c307, some c101, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p734 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 31) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c114, c171, c307, c101] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c733, some c166, some c729, some c158, some c251, some c732, some c154, some c108, some c212, some c114, some c38, some c117, some c734, some c21, some c234, some c98, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p735 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 31) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c681, c733, c166, c729, c158, c251, c732, c154, c108, c212, c114, c38, c117, c734, c21, c234, c98] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c733 := derived733 a h
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c729 := derived729 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c732 := derived732 a h
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c735, some c729, some c158, some c108, some c494, some c380, some c21, some c23, some c69, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p736 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 31) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c681, c735, c729, c158, c108, c494, c380, c21, c23, c69] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c735 := derived735 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c494 := h 493 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c729, some c158, some c166, some c735, some c736, some c496, some c382, some c21, some c23, some c69, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p737 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 31) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c681, c729, c158, c166, c735, c736, c496, c382, c21, c23, c69] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c735 := derived735 a h
  have h5 : Entails.eval a c736 := derived736 a h
  have h6 : Entails.eval a c496 := h 495 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c729, some c158, some c737, some c179, some c10, some c201, some c246, some c279, some c242, some c47, some c117, some c45, some c200, some c38, some c113, some c202, some c119, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p738 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 31) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c681, c729, c158, c737, c179, c10, c201, c246, c279, c242, c47, c117, c45, c200, c38, c113, c202, c119] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c279 := h 278 (by decide)
  have h9 : Entails.eval a c242 := h 241 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c729, some c262, some c222, some c73, some c201, some c279, some c246, some c254, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p739 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 31) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c681, c738, c729, c262, c222, c73, c201, c279, c246, c254] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c272, some c165, some c693, some c695, some c212, some c694, some c117, some c351, some c131, some c139, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p740 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 31) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c681, c738, c739, c272, c165, c693, c695, c212, c694, c117, c351, c131, c139] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c693 := derived693 a h
  have h6 : Entails.eval a c695 := derived695 a h
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c694 := derived694 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c740, some c738, some c739, some c272, some c729, some c212, some c630, some c225, some c119, some c496, some c501, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p741 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 31) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c681, c740, c738, c739, c272, c729, c212, c630, c225, c119, c496, c501] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c740 := derived740 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c729 := derived729 a h
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c630 := derived630 a h
  have h8 : Entails.eval a c225 := h 224 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c496 := h 495 (by decide)
  have h11 : Entails.eval a c501 := h 500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c741, some c336, some c691, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p742 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 31) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c681, c738, c741, c336, c691] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c741 := derived741 a h
  have h3 : Entails.eval a c336 := h 335 (by decide)
  have h4 : Entails.eval a c691 := derived691 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c742, some c408, some c515, some c298, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p743 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 31) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c681, c738, c739, c165, c742, c408, c515, c298] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c742 := derived742 a h
  have h5 : Entails.eval a c408 := h 407 (by decide)
  have h6 : Entails.eval a c515 := h 514 (by decide)
  have h7 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c729, some c272, some c743, some c730, some c692, some c225, some c118, some c212, some c445, some c515, some c238, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p744 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 31) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c681, c738, c739, c165, c729, c272, c743, c730, c692, c225, c118, c212, c445, c515, c238] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c743 := derived743 a h
  have h7 : Entails.eval a c730 := derived730 a h
  have h8 : Entails.eval a c692 := derived692 a h
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c445 := h 444 (by decide)
  have h13 : Entails.eval a c515 := h 514 (by decide)
  have h14 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c729, some c744, some c245, some c246, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p745 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 31) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c681, c738, c739, c165, c729, c744, c245, c246] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c744 := derived744 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c745, some c738, some c739, some c165, some c729, some c249, some c271, some c229, some c119, some c204, some c403, some c213, some c75, some c74, some c338, some c122, some c137, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p746 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 31) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c681, c745, c738, c739, c165, c729, c249, c271, c229, c119, c204, c403, c213, c75, c74, c338, c122, c137] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c729 := derived729 a h
  have h6 : Entails.eval a c249 := h 248 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c403 := h 402 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c745, some c738, some c739, some c165, some c729, some c746, some c272, some c271, some c225, some c212, some c75, some c610, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p747 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 31) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c681, c745, c738, c739, c165, c729, c746, c272, c271, c225, c212, c75, c610] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c729 := derived729 a h
  have h6 : Entails.eval a c746 := derived746 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c610 := derived610 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c729, some c747, some c245, some c272, some c745, some c370, some c458, some c610, some c338, some c268, some c408, some c236, some c150, some c227, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p748 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 31) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c681, c738, c739, c165, c729, c747, c245, c272, c745, c370, c458, c610, c338, c268, c408, c236, c150, c227] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c747 := derived747 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c745 := derived745 a h
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c458 := h 457 (by decide)
  have h11 : Entails.eval a c610 := derived610 a h
  have h12 : Entails.eval a c338 := h 337 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c408 := h 407 (by decide)
  have h15 : Entails.eval a c236 := h 235 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c729, some c747, some c245, some c272, some c745, some c748, some c77, some c225, some c119, some c394, some c356, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p749 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 31) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c681, c738, c739, c165, c729, c747, c245, c272, c745, c748, c77, c225, c119, c394, c356] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c747 := derived747 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c745 := derived745 a h
  have h9 : Entails.eval a c748 := derived748 a h
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c225 := h 224 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c394 := h 393 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c738, some c739, some c165, some c729, some c745, some c747, some c245, some c272, some c749, some c212, some c77, some c225, some c119, some c356, some c468, some c411, some c426, some c90, some c321, some c319, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p750 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 31) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c681, c738, c739, c165, c729, c745, c747, c245, c272, c749, c212, c77, c225, c119, c356, c468, c411, c426, c90, c321, c319] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c738 := derived738 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c745 := derived745 a h
  have h6 : Entails.eval a c747 := derived747 a h
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c749 := derived749 a h
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c225 := h 224 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c468 := h 467 (by decide)
  have h16 : Entails.eval a c411 := h 410 (by decide)
  have h17 : Entails.eval a c426 := h 425 (by decide)
  have h18 : Entails.eval a c90 := h 89 (by decide)
  have h19 : Entails.eval a c321 := h 320 (by decide)
  have h20 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c750, some c739, some c19, some c738, some c73, some c645, some c112, some c165, some c729, some c271, some c120, some c88, some c118, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p751 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 31) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c681, c750, c739, c19, c738, c73, c645, c112, c165, c729, c271, c120, c88, c118] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c738 := derived738 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c729 := derived729 a h
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c729, some c738, some c739, some c165, some c750, some c19, some c73, some c112, some c645, some c212, some c751, some c129, some c118, some c607, some c514, some c291, some c506, some c318, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p752 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 31) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c681, c729, c738, c739, c165, c750, c19, c73, c112, c645, c212, c751, c129, c118, c607, c514, c291, c506, c318] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c750 := derived750 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c645 := derived645 a h
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c751 := derived751 a h
  have h12 : Entails.eval a c129 := h 128 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c607 := derived607 a h
  have h15 : Entails.eval a c514 := h 513 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c506 := h 505 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c88, some c118, some c207, some c212, some c251, some c607, some c291, some c23, some c83, some c270, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p753 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 31) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c681, c88, c118, c207, c212, c251, c607, c291, c23, c83, c270] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c607 := derived607 a h
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c165, some c212, some c251, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p754 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 31) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c681, c165, c212, c251] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c753, some c754, some c10, some c247, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p755 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 31) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c753, c754, c10, c247] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c753 := derived753 a h
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c112, some c205, some c154, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p756 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 31) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c681, c112, c205, c154] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c756, some c755, some c207, some c212, some c754, some c251, some c129, some c607, some c74, some c291, some c106, some c462, some c23, some c358, some c368, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p757 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 31) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c681, c756, c755, c207, c212, c754, c251, c129, c607, c74, c291, c106, c462, c23, c358, c368] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c755 := derived755 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c754 := derived754 a h
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c462 := h 461 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived757

end CochromaticTwenty.Certificates.Z12Direct_5_8_9
