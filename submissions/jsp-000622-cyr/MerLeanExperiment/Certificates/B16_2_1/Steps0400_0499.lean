import MerLeanExperiment.Certificates.B16_2_1.Steps0300_0399

/-! Generated from the actual pinned b16_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c723 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c710, some c311, some c316, some c709, some c80, some c217, some c99, some c30, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c622, c710, c311, c316, c709, c80, c217, c99, c30] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c710 := derived710 a h
  have h2 : Entails.eval a c311 := h 310 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c709 := derived709 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c705, some c707, some c60, some c714, some c720, some c722, some c68, some c306, some c307, some c69, some c297, some c295, some c723, some c3, some c373, some c511, some c2, some c636, some c318, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c622, c683, c705, c707, c60, c714, c720, c722, c68, c306, c307, c69, c297, c295, c723, c3, c373, c511, c2, c636, c318] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c707 := derived707 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c714 := derived714 a h
  have h6 : Entails.eval a c720 := derived720 a h
  have h7 : Entails.eval a c722 := derived722 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c295 := h 294 (by decide)
  have h14 : Entails.eval a c723 := derived723 a h
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c373 := derived373 a h
  have h17 : Entails.eval a c511 := derived511 a h
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c636 := derived636 a h
  have h20 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c724, some c683, some c3, some c62, some c682, some c170, some c169, some c60, some c68, some c8, some c168, some c305, some c304, some c219, some c69, some c211, some c636, some c217, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c622, c724, c683, c3, c62, c682, c170, c169, c60, c68, c8, c168, c305, c304, c219, c69, c211, c636, c217] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c724 := derived724 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c682 := derived682 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c219 := h 218 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c636 := derived636 a h
  have h18 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c67, some c80, some c300, some c316, some c68, some c583, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c622, c67, c80, c300, c316, c68, c583] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c725, some c724, some c683, some c710, some c311, some c21, some c726, some c99, some c63, some c22, some c217, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c725, c724, c683, c710, c311, c21, c726, c99, c63, c22, c217] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c725 := derived725 a h
  have h1 : Entails.eval a c724 := derived724 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c710 := derived710 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c726 := derived726 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c725, some c60, some c78, some c316, some c317, some c574, some c419, some c8, some c67, some c145, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c622, c725, c60, c78, c316, c317, c574, c419, c8, c67, c145] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c725 := derived725 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c574 := derived574 a h
  have h7 : Entails.eval a c419 := derived419 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c299, some c300, some c298, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c622, c299, c300, c298] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c725, some c728, some c710, some c311, some c727, some c21, some c729, some c68, some c69, some c304, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c683, c725, c728, c710, c311, c727, c21, c729, c68, c69, c304] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c725 := derived725 a h
  have h2 : Entails.eval a c728 := derived728 a h
  have h3 : Entails.eval a c710 := derived710 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c727 := derived727 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c729 := derived729 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c730, some c683, some c710, some c311, some c717, some c21, some c729, some c69, some c304, some c309, some c291, some c316, some c657, some c633, some c84, some c31, some c218, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c622, c730, c683, c710, c311, c717, c21, c729, c69, c304, c309, c291, c316, c657, c633, c84, c31, c218] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c730 := derived730 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c710 := derived710 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c717 := derived717 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c729 := derived729 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c657 := derived657 a h
  have h14 : Entails.eval a c633 := derived633 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c730, some c724, some c683, some c71, some c21, some c96, some c100, some c72, some c13, some c143, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c730, c724, c683, c71, c21, c96, c100, c72, c13, c143] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c730 := derived730 a h
  have h1 : Entails.eval a c724 := derived724 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c662, some c300, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c662, c300] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c662 := derived662 a h
  have h1 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c730, some c731, some c60, some c732, some c733, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c730, c731, c60, c732, c733] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c730 := derived730 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c732 := derived732 a h
  have h4 : Entails.eval a c733 := derived733 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c730, some c734, some c3, some c682, some c721, some c170, some c169, some c60, some c315, some c168, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c622, c730, c734, c3, c682, c721, c170, c169, c60, c315, c168] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c730 := derived730 a h
  have h2 : Entails.eval a c734 := derived734 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c682 := derived682 a h
  have h5 : Entails.eval a c721 := derived721 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c169 := h 168 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c735, some c1, some c683, some c313, some c218, some c633, some c372, some c33, some c31, some c10, some c110, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c3, c735, c1, c683, c313, c218, c633, c372, c33, c31, c10, c110] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c735 := derived735 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c633 := derived633 a h
  have h7 : Entails.eval a c372 := derived372 a h
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c3, some c724, some c736, some c82, some c673, some c97, some c152, some c7, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c62, c3, c724, c736, c82, c673, c97, c152, c7] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c736 := derived736 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c673 := derived673 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c1, some c724, some c683, some c737, some c315, some c82, some c96, some c81, some c22, some c217, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c735, c1, c724, c683, c737, c315, c82, c96, c81, c22, c217] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c737 := derived737 a h
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c735, some c1, some c683, some c738, some c311, some c216, some c717, some c21, some c69, some c304, some c309, some c291, some c316, some c657, some c633, some c84, some c31, some c218, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c622, c735, c1, c683, c738, c311, c216, c717, c21, c69, c304, c309, c291, c316, c657, c633, c84, c31, c218] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c735 := derived735 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c738 := derived738 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c657 := derived657 a h
  have h15 : Entails.eval a c633 := derived633 a h
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c1, some c724, some c683, some c739, some c9, some c68, some c373, some c311, some c216, some c21, some c726, some c305, some c304, some c294, some c69, some c217, some c99, some c22, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c735, c1, c724, c683, c739, c9, c68, c373, c311, c216, c21, c726, c305, c304, c294, c69, c217, c99, c22] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c739 := derived739 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c373 := derived373 a h
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c726 := derived726 a h
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  have h17 : Entails.eval a c99 := h 98 (by decide)
  have h18 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c216, some c729, some c21, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c311, c216, c729, c21] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c1, some c740, some c683, some c741, some c62, some c729, some c315, some c9, some c373, some c437, some c61, some c20, some c81, some c666, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c735, c1, c740, c683, c741, c62, c729, c315, c9, c373, c437, c61, c20, c81, c666] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c740 := derived740 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c741 := derived741 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c729 := derived729 a h
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c373 := derived373 a h
  have h10 : Entails.eval a c437 := derived437 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c735, some c1, some c740, some c741, some c742, some c738, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c683, c735, c1, c740, c741, c742, c738] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c735 := derived735 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c740 := derived740 a h
  have h4 : Entails.eval a c741 := derived741 a h
  have h5 : Entails.eval a c742 := derived742 a h
  have h6 : Entails.eval a c738 := derived738 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c683, some c292, some c217, some c313, some c209, some c293, some c234, some c303, some c211, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c724, c683, c292, c217, c313, c209, c293, c234, c303, c211] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c217 := h 216 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c234 := h 233 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c683, some c744, some c729, some c299, some c300, some c219, some c215, some c211, some c237, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c724, c683, c744, c729, c299, c300, c219, c215, c211, c237] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c744 := derived744 a h
  have h3 : Entails.eval a c729 := derived729 a h
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c219 := h 218 (by decide)
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c683, some c211, some c215, some c237, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c724, c683, c211, c215, c237] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c78, some c291, some c671, some c304, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c622, c743, c78, c291, c671, c304] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c745, some c1, some c743, some c729, some c299, some c300, some c141, some c67, some c442, some c747, some c318, some c320, some c496, some c162, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c622, c745, c1, c743, c729, c299, c300, c141, c67, c442, c747, c318, c320, c496, c162] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c743 := derived743 a h
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c442 := derived442 a h
  have h10 : Entails.eval a c747 := derived747 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c496 := derived496 a h
  have h14 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c67, some c98, some c724, some c683, some c746, some c673, some c234, some c238, some c33, some c649, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c622, c743, c67, c98, c724, c683, c746, c673, c234, c238, c33, c649] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c724 := derived724 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c746 := derived746 a h
  have h7 : Entails.eval a c673 := derived673 a h
  have h8 : Entails.eval a c234 := h 233 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c649 := derived649 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c743, some c98, some c724, some c649, some c229, some c22, some c96, some c680, some c628, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c743, c98, c724, c649, c229, c22, c96, c680, c628] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c743 := derived743 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c680 := derived680 a h
  have h8 : Entails.eval a c628 := derived628 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, false), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c1, some c743, some c683, some c67, some c98, some c442, some c318, some c78, some c94, some c749, some c303, some c144, some c297, some c7, some c16, some c750, some c34, some c234, some c238, some c210, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c622, c1, c743, c683, c67, c98, c442, c318, c78, c94, c749, c303, c144, c297, c7, c16, c750, c34, c234, c238, c210] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c743 := derived743 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c442 := derived442 a h
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c749 := derived749 a h
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c750 := derived750 a h
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c234 := h 233 (by decide)
  have h19 : Entails.eval a c238 := h 237 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c743, some c94, some c724, some c683, some c34, some c234, some c238, some c210, some c33, some c303, some c673, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c743, c94, c724, c683, c34, c234, c238, c210, c33, c303, c673] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c743 := derived743 a h
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c234 := h 233 (by decide)
  have h6 : Entails.eval a c238 := h 237 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c673 := derived673 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c724, some c683, some c745, some c1, some c748, some c292, some c751, some c145, some c8, some c98, some c442, some c318, some c78, some c94, some c752, some c649, some c229, some c235, some c234, some c100, some c239, some c22, some c211, some c669, some c96, some c303, some c144, some c668, some c65, some c7, some c628, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c622, c743, c724, c683, c745, c1, c748, c292, c751, c145, c8, c98, c442, c318, c78, c94, c752, c649, c229, c235, c234, c100, c239, c22, c211, c669, c96, c303, c144, c668, c65, c7, c628] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c745 := derived745 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c748 := derived748 a h
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c751 := derived751 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c442 := derived442 a h
  have h13 : Entails.eval a c318 := h 317 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c752 := derived752 a h
  have h17 : Entails.eval a c649 := derived649 a h
  have h18 : Entails.eval a c229 := h 228 (by decide)
  have h19 : Entails.eval a c235 := h 234 (by decide)
  have h20 : Entails.eval a c234 := h 233 (by decide)
  have h21 : Entails.eval a c100 := h 99 (by decide)
  have h22 : Entails.eval a c239 := h 238 (by decide)
  have h23 : Entails.eval a c22 := h 21 (by decide)
  have h24 : Entails.eval a c211 := h 210 (by decide)
  have h25 : Entails.eval a c669 := derived669 a h
  have h26 : Entails.eval a c96 := h 95 (by decide)
  have h27 : Entails.eval a c303 := h 302 (by decide)
  have h28 : Entails.eval a c144 := h 143 (by decide)
  have h29 : Entails.eval a c668 := derived668 a h
  have h30 : Entails.eval a c65 := h 64 (by decide)
  have h31 : Entails.eval a c7 := h 6 (by decide)
  have h32 : Entails.eval a c628 := derived628 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c753, some c60, some c743, some c724, some c683, some c292, some c217, some c313, some c22, some c209, some c293, some c235, some c234, some c211, some c308, some c68, some c93, some c94, some c96, some c69, some c36, some c34, some c692, some c554, some c291, some c16, some c157, some c680, some c161, some c176, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c622, c753, c60, c743, c724, c683, c292, c217, c313, c22, c209, c293, c235, c234, c211, c308, c68, c93, c94, c96, c69, c36, c34, c692, c554, c291, c16, c157, c680, c161, c176] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c743 := derived743 a h
  have h4 : Entails.eval a c724 := derived724 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c217 := h 216 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c234 := h 233 (by decide)
  have h14 : Entails.eval a c211 := h 210 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c68 := h 67 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c94 := h 93 (by decide)
  have h19 : Entails.eval a c96 := h 95 (by decide)
  have h20 : Entails.eval a c69 := h 68 (by decide)
  have h21 : Entails.eval a c36 := h 35 (by decide)
  have h22 : Entails.eval a c34 := h 33 (by decide)
  have h23 : Entails.eval a c692 := derived692 a h
  have h24 : Entails.eval a c554 := derived554 a h
  have h25 : Entails.eval a c291 := h 290 (by decide)
  have h26 : Entails.eval a c16 := h 15 (by decide)
  have h27 : Entails.eval a c157 := h 156 (by decide)
  have h28 : Entails.eval a c680 := derived680 a h
  have h29 : Entails.eval a c161 := h 160 (by decide)
  have h30 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c304, some c309, some c291, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c622, c304, c309, c291] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c754, some c753, some c743, some c755, some c69, some c93, some c98, some c80, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c622, c754, c753, c743, c755, c69, c93, c98, c80] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c743 := derived743 a h
  have h4 : Entails.eval a c755 := derived755 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c235, some c239, some c29, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c235, c239, c29] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c235 := h 234 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c754, some c305, some c756, some c753, some c60, some c724, some c683, some c223, some c241, some c583, some c211, some c219, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c754, c305, c756, c753, c60, c724, c683, c223, c241, c583, c211, c219] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c754 := derived754 a h
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c724 := derived724 a h
  have h6 : Entails.eval a c683 := derived683 a h
  have h7 : Entails.eval a c223 := h 222 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c583 := derived583 a h
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c98, some c8, some c753, some c93, some c68, some c724, some c683, some c757, some c758, some c29, some c237, some c116, some c22, some c336, some c121, some c45, some c47, some c191, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c622, c743, c98, c8, c753, c93, c68, c724, c683, c757, c758, c29, c237, c116, c22, c336, c121, c45, c47, c191] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c753 := derived753 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c724 := derived724 a h
  have h8 : Entails.eval a c683 := derived683 a h
  have h9 : Entails.eval a c757 := derived757 a h
  have h10 : Entails.eval a c758 := derived758 a h
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c336 := derived336 a h
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c756, some c754, some c753, some c60, some c743, some c724, some c683, some c93, some c68, some c304, some c305, some c759, some c213, some c219, some c529, some c583, some c318, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c756, c754, c753, c60, c743, c724, c683, c93, c68, c304, c305, c759, c213, c219, c529, c583, c318] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c756 := derived756 a h
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c743 := derived743 a h
  have h5 : Entails.eval a c724 := derived724 a h
  have h6 : Entails.eval a c683 := derived683 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c759 := derived759 a h
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c529 := derived529 a h
  have h15 : Entails.eval a c583 := derived583 a h
  have h16 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c219, some c238, some c85, some c33, some c318, some c633, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c34, c219, c238, c85, c33, c318, c633] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c753, some c60, some c756, some c760, some c754, some c69, some c304, some c68, some c743, some c94, some c761, some c309, some c67, some c724, some c219, some c234, some c238, some c66, some c7, some c85, some c103, some c318, some c10, some c633, some c83, some c538, some c554, some c24, some c180, some c176, some c113, some c158, some c351, some c126, some c132, some c264, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c622, c683, c753, c60, c756, c760, c754, c69, c304, c68, c743, c94, c761, c309, c67, c724, c219, c234, c238, c66, c7, c85, c103, c318, c10, c633, c83, c538, c554, c24, c180, c176, c113, c158, c351, c126, c132, c264] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c756 := derived756 a h
  have h5 : Entails.eval a c760 := derived760 a h
  have h6 : Entails.eval a c754 := derived754 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c743 := derived743 a h
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c761 := derived761 a h
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c724 := derived724 a h
  have h16 : Entails.eval a c219 := h 218 (by decide)
  have h17 : Entails.eval a c234 := h 233 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c7 := h 6 (by decide)
  have h21 : Entails.eval a c85 := h 84 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  have h23 : Entails.eval a c318 := h 317 (by decide)
  have h24 : Entails.eval a c10 := h 9 (by decide)
  have h25 : Entails.eval a c633 := derived633 a h
  have h26 : Entails.eval a c83 := h 82 (by decide)
  have h27 : Entails.eval a c538 := derived538 a h
  have h28 : Entails.eval a c554 := derived554 a h
  have h29 : Entails.eval a c24 := h 23 (by decide)
  have h30 : Entails.eval a c180 := h 179 (by decide)
  have h31 : Entails.eval a c176 := h 175 (by decide)
  have h32 : Entails.eval a c113 := h 112 (by decide)
  have h33 : Entails.eval a c158 := h 157 (by decide)
  have h34 : Entails.eval a c351 := derived351 a h
  have h35 : Entails.eval a c126 := h 125 (by decide)
  have h36 : Entails.eval a c132 := h 131 (by decide)
  have h37 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c754, some c753, some c760, some c69, some c309, some c67, some c683, some c304, some c756, some c60, some c68, some c743, some c94, some c761, some c223, some c208, some c235, some c724, some c318, some c63, some c237, some c351, some c96, some c762, some c25, some c7, some c538, some c554, some c218, some c24, some c158, some c15, some c116, some c176, some c132, some c126, some c264, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c622, c754, c753, c760, c69, c309, c67, c683, c304, c756, c60, c68, c743, c94, c761, c223, c208, c235, c724, c318, c63, c237, c351, c96, c762, c25, c7, c538, c554, c218, c24, c158, c15, c116, c176, c132, c126, c264] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c760 := derived760 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c683 := derived683 a h
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c756 := derived756 a h
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c743 := derived743 a h
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c761 := derived761 a h
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c208 := h 207 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c724 := derived724 a h
  have h19 : Entails.eval a c318 := h 317 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c351 := derived351 a h
  have h23 : Entails.eval a c96 := h 95 (by decide)
  have h24 : Entails.eval a c762 := derived762 a h
  have h25 : Entails.eval a c25 := h 24 (by decide)
  have h26 : Entails.eval a c7 := h 6 (by decide)
  have h27 : Entails.eval a c538 := derived538 a h
  have h28 : Entails.eval a c554 := derived554 a h
  have h29 : Entails.eval a c218 := h 217 (by decide)
  have h30 : Entails.eval a c24 := h 23 (by decide)
  have h31 : Entails.eval a c158 := h 157 (by decide)
  have h32 : Entails.eval a c15 := h 14 (by decide)
  have h33 : Entails.eval a c116 := h 115 (by decide)
  have h34 : Entails.eval a c176 := h 175 (by decide)
  have h35 : Entails.eval a c132 := h 131 (by decide)
  have h36 : Entails.eval a c126 := h 125 (by decide)
  have h37 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c753, some c754, some c760, some c69, some c304, some c68, some c94, some c762, some c25, some c683, some c60, some c756, some c761, some c309, some c67, some c724, some c318, some c223, some c63, some c208, some c96, some c237, some c235, some c351, some c763, some c315, some c6, some c554, some c16, some c151, some c116, some c162, some c133, some c177, some c265, some c126, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c622, c743, c753, c754, c760, c69, c304, c68, c94, c762, c25, c683, c60, c756, c761, c309, c67, c724, c318, c223, c63, c208, c96, c237, c235, c351, c763, c315, c6, c554, c16, c151, c116, c162, c133, c177, c265, c126] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c753 := derived753 a h
  have h3 : Entails.eval a c754 := derived754 a h
  have h4 : Entails.eval a c760 := derived760 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c762 := derived762 a h
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c683 := derived683 a h
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c756 := derived756 a h
  have h14 : Entails.eval a c761 := derived761 a h
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c724 := derived724 a h
  have h18 : Entails.eval a c318 := h 317 (by decide)
  have h19 : Entails.eval a c223 := h 222 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c96 := h 95 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c235 := h 234 (by decide)
  have h25 : Entails.eval a c351 := derived351 a h
  have h26 : Entails.eval a c763 := derived763 a h
  have h27 : Entails.eval a c315 := h 314 (by decide)
  have h28 : Entails.eval a c6 := h 5 (by decide)
  have h29 : Entails.eval a c554 := derived554 a h
  have h30 : Entails.eval a c16 := h 15 (by decide)
  have h31 : Entails.eval a c151 := h 150 (by decide)
  have h32 : Entails.eval a c116 := h 115 (by decide)
  have h33 : Entails.eval a c162 := h 161 (by decide)
  have h34 : Entails.eval a c133 := h 132 (by decide)
  have h35 : Entails.eval a c177 := h 176 (by decide)
  have h36 : Entails.eval a c265 := h 264 (by decide)
  have h37 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c743, some c724, some c683, some c753, some c60, some c754, some c756, some c760, some c69, some c304, some c68, some c94, some c762, some c764, some c85, some c315, some c674, some c692, some c96, some c63, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c743, c724, c683, c753, c60, c754, c756, c760, c69, c304, c68, c94, c762, c764, c85, c315, c674, c692, c96, c63] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c743 := derived743 a h
  have h1 : Entails.eval a c724 := derived724 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c754 := derived754 a h
  have h6 : Entails.eval a c756 := derived756 a h
  have h7 : Entails.eval a c760 := derived760 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c762 := derived762 a h
  have h13 : Entails.eval a c764 := derived764 a h
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c674 := derived674 a h
  have h17 : Entails.eval a c692 := derived692 a h
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c683, some c729, some c303, some c209, some c210, some c236, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c724, c683, c729, c303, c209, c210, c236] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c209 := h 208 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨45, by decide⟩, false), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c683, some c766, some c68, some c304, some c308, some c209, some c210, some c236, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c724, c683, c766, c68, c304, c308, c209, c210, c236] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c765, some c743, some c724, some c683, some c316, some c317, some c79, some c64, some c85, some c216, some c94, some c767, some c298, some c294, some c309, some c217, some c209, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c622, c765, c743, c724, c683, c316, c317, c79, c64, c85, c216, c94, c767, c298, c294, c309, c217, c209] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c765 := derived765 a h
  have h2 : Entails.eval a c743 := derived743 a h
  have h3 : Entails.eval a c724 := derived724 a h
  have h4 : Entails.eval a c683 := derived683 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c767 := derived767 a h
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c768, some c729, some c755, some c69, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c768, c729, c755, c69] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c768 := derived768 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c755 := derived755 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c765, some c743, some c724, some c683, some c311, some c216, some c769, some c209, some c217, some c236, some c63, some c294, some c210, some c766, some c308, some c68, some c94, some c96, some c87, some c33, some c649, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c622, c765, c743, c724, c683, c311, c216, c769, c209, c217, c236, c63, c294, c210, c766, c308, c68, c94, c96, c87, c33, c649] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c765 := derived765 a h
  have h2 : Entails.eval a c743 := derived743 a h
  have h3 : Entails.eval a c724 := derived724 a h
  have h4 : Entails.eval a c683 := derived683 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c769 := derived769 a h
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c766 := derived766 a h
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c68 := h 67 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c33 := h 32 (by decide)
  have h21 : Entails.eval a c649 := derived649 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c765, some c724, some c768, some c770, some c60, some c79, some c78, some c733, some c752, some c226, some c651, some c649, some c67, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c622, c765, c724, c768, c770, c60, c79, c78, c733, c752, c226, c651, c649, c67] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c765 := derived765 a h
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c768 := derived768 a h
  have h4 : Entails.eval a c770 := derived770 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c733 := derived733 a h
  have h9 : Entails.eval a c752 := derived752 a h
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c651 := derived651 a h
  have h12 : Entails.eval a c649 := derived649 a h
  have h13 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c743, some c771, some c98, some c67, some c8, some c60, some c1, some c145, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c622, c743, c771, c98, c67, c8, c60, c1, c145] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c771 := derived771 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c724, some c743, some c765, some c771, some c93, some c98, some c80, some c317, some c726, some c772, some c216, some c209, some c217, some c236, some c294, some c210, some c766, some c308, some c68, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c622, c683, c724, c743, c765, c771, c93, c98, c80, c317, c726, c772, c216, c209, c217, c236, c294, c210, c766, c308, c68] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c724 := derived724 a h
  have h3 : Entails.eval a c743 := derived743 a h
  have h4 : Entails.eval a c765 := derived765 a h
  have h5 : Entails.eval a c771 := derived771 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c726 := derived726 a h
  have h11 : Entails.eval a c772 := derived772 a h
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c217 := h 216 (by decide)
  have h15 : Entails.eval a c236 := h 235 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c766 := derived766 a h
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c89, some c88, some c87, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c773, c622, c89, c88, c87] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c774, some c12, some c91, some c90, some c86, some c13, some c313, some c173, some c164, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c773, c622, c774, c12, c91, c90, c86, c13, c313, c173, c164] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c774 := derived774 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c775, some c315, some c311, some c3, some c89, some c88, some c86, some c457, some c90, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c773, c622, c775, c315, c311, c3, c89, c88, c86, c457, c90] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c457 := derived457 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨16, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c172, some c170, some c776, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c172, c170, c776] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c776 := derived776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨15, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c774, some c88, some c158, some c73, some c25, some c310, some c307, some c219, some c671, some c206, some c61, some c225, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c773, c774, c88, c158, c73, c25, c310, c307, c219, c671, c206, c61, c225] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c774 := derived774 a h
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c671 := derived671 a h
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c3, some c162, some c89, some c88, some c313, some c86, some c163, some c90, some c14, some c178, some c778, some c293, some c309, some c295, some c318, some c2, some c463, some c464, some c93, some c186, some c23, some c117, some c229, some c32, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c622, c773, c3, c162, c89, c88, c313, c86, c163, c90, c14, c178, c778, c293, c309, c295, c318, c2, c463, c464, c93, c186, c23, c117, c229, c32] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c778 := derived778 a h
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c309 := h 308 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c463 := derived463 a h
  have h19 : Entails.eval a c464 := derived464 a h
  have h20 : Entails.eval a c93 := h 92 (by decide)
  have h21 : Entails.eval a c186 := h 185 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c117 := h 116 (by decide)
  have h24 : Entails.eval a c229 := h 228 (by decide)
  have h25 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c311, some c774, some c12, some c127, some c120, some c261, some c50, some c118, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c773, c311, c774, c12, c127, c120, c261, c50, c118] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c774 := derived774 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c779, some c311, some c774, some c12, some c91, some c90, some c86, some c13, some c313, some c164, some c178, some c780, some c38, some c596, some c118, some c124, some c80, some c280, some c263, some c119, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c622, c773, c779, c311, c774, c12, c91, c90, c86, c13, c313, c164, c178, c780, c38, c596, c118, c124, c80, c280, c263, c119] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c779 := derived779 a h
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c780 := derived780 a h
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c596 := derived596 a h
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c80, some c29, some c221, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c622, c80, c29, c221] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c311, some c774, some c21, some c91, some c90, some c86, some c72, some c35, some c313, some c164, some c175, some c782, some c95, some c597, some c15, some c580, some c158, some c307, some c294, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c622, c773, c311, c774, c21, c91, c90, c86, c72, c35, c313, c164, c175, c782, c95, c597, c15, c580, c158, c307, c294] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c311 := h 310 (by decide)
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c175 := h 174 (by decide)
  have h13 : Entails.eval a c782 := derived782 a h
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c597 := derived597 a h
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c580 := derived580 a h
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c307 := h 306 (by decide)
  have h20 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c777, some c781, some c153, some c179, some c311, some c774, some c21, some c216, some c112, some c783, some c4, some c71, some c313, some c310, some c207, some c226, some c239, some c295, some c206, some c307, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c777, c781, c153, c179, c311, c774, c21, c216, c112, c783, c4, c71, c313, c310, c207, c226, c239, c295, c206, c307] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c777 := derived777 a h
  have h1 : Entails.eval a c781 := derived781 a h
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c774 := derived774 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c783 := derived783 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c310 := h 309 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c295 := h 294 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c777, some c781, some c179, some c153, some c784, some c62, some c89, some c88, some c774, some c315, some c293, some c86, some c90, some c4, some c14, some c778, some c175, some c165, some c318, some c2, some c463, some c464, some c122, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c622, c773, c777, c781, c179, c153, c784, c62, c89, c88, c774, c315, c293, c86, c90, c4, c14, c778, c175, c165, c318, c2, c463, c464, c122] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c781 := derived781 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c784 := derived784 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c774 := derived774 a h
  have h11 : Entails.eval a c315 := h 314 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c778 := derived778 a h
  have h18 : Entails.eval a c175 := h 174 (by decide)
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c318 := h 317 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c463 := derived463 a h
  have h23 : Entails.eval a c464 := derived464 a h
  have h24 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨12, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c62, some c292, some c89, some c88, some c313, some c293, some c86, some c90, some c22, some c73, some c217, some c308, some c206, some c222, some c106, some c2, some c466, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c622, c773, c62, c292, c89, c88, c313, c293, c86, c90, c22, c73, c217, c308, c206, c222, c106, c2, c466] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c292 := h 291 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c222 := h 221 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c785, some c180, some c156, some c777, some c153, some c786, some c311, some c774, some c21, some c71, some c112, some c91, some c90, some c782, some c35, some c95, some c611, some c15, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c773, c785, c180, c156, c777, c153, c786, c311, c774, c21, c71, c112, c91, c90, c782, c35, c95, c611, c15] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c777 := derived777 a h
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c786 := derived786 a h
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c774 := derived774 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c782 := derived782 a h
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c611 := derived611 a h
  have h18 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c177, some c90, some c311, some c774, some c21, some c72, some c216, some c308, some c206, some c239, some c221, some c2, some c95, some c611, some c33, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c773, c177, c90, c311, c774, c21, c72, c216, c308, c206, c239, c221, c2, c95, c611, c33] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c611 := derived611 a h
  have h15 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c177, some c90, some c91, some c611, some c597, some c35, some c115, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c773, c177, c90, c91, c611, c597, c35, c115] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c597 := derived597 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨44, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c311, some c774, some c777, some c91, some c90, some c86, some c13, some c313, some c294, some c788, some c305, some c789, some c80, some c20, some c224, some c221, some c31, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c773, c622, c311, c774, c777, c91, c90, c86, c13, c313, c294, c788, c305, c789, c80, c20, c224, c221, c31] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c311 := h 310 (by decide)
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c777 := derived777 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c788 := derived788 a h
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c789 := derived789 a h
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c785, some c156, some c311, some c774, some c790, some c71, some c22, some c63, some c309, some c217, some c207, some c229, some c241, some c583, some c206, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c787, c785, c156, c311, c774, c790, c71, c22, c63, c309, c217, c207, c229, c241, c583, c206] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c790 := derived790 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c241 := h 240 (by decide)
  have h14 : Entails.eval a c583 := derived583 a h
  have h15 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c785, some c156, some c787, some c791, some c3, some c89, some c88, some c774, some c315, some c163, some c86, some c177, some c90, some c466, some c22, some c63, some c80, some c115, some c222, some c29, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c622, c773, c785, c156, c787, c791, c3, c89, c88, c774, c315, c163, c86, c177, c90, c466, c22, c63, c80, c115, c222, c29] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c791 := derived791 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c774 := derived774 a h
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c466 := derived466 a h
  have h16 : Entails.eval a c22 := h 21 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c115 := h 114 (by decide)
  have h20 : Entails.eval a c222 := h 221 (by decide)
  have h21 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c792, some c8, some c91, some c89, some c71, some c22, some c63, some c309, some c217, some c207, some c229, some c241, some c583, some c206, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c622, c773, c792, c8, c91, c89, c71, c22, c63, c309, c217, c207, c229, c241, c583, c206] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c241 := h 240 (by decide)
  have h14 : Entails.eval a c583 := derived583 a h
  have h15 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false), (⟨12, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c167, some c155, some c177, some c295, some c161, some c316, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c622, c167, c155, c177, c295, c161, c316] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c792, some c8, some c91, some c89, some c3, some c12, some c311, some c793, some c310, some c794, some c313, some c542, some c13, some c155, some c177, some c72, some c24, some c161, some c218, some c316, some c224, some c583, some c206, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c773, c622, c792, c8, c91, c89, c3, c12, c311, c793, c310, c794, c313, c542, c13, c155, c177, c72, c24, c161, c218, c316, c224, c583, c206] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c793 := derived793 a h
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c794 := derived794 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c542 := derived542 a h
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c177 := h 176 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c316 := h 315 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c583 := derived583 a h
  have h24 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c795, some c792, some c8, some c89, some c311, some c168, some c793, some c175, some c310, some c161, some c316, some c296, some c152, some c21, some c216, some c221, some c206, some c307, some c72, some c295, some c542, some c313, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c622, c773, c795, c792, c8, c89, c311, c168, c793, c175, c310, c161, c316, c296, c152, c21, c216, c221, c206, c307, c72, c295, c542, c313] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c795 := derived795 a h
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c793 := derived793 a h
  have h9 : Entails.eval a c175 := h 174 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c216 := h 215 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c307 := h 306 (by decide)
  have h20 : Entails.eval a c72 := h 71 (by decide)
  have h21 : Entails.eval a c295 := h 294 (by decide)
  have h22 : Entails.eval a c542 := derived542 a h
  have h23 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c168, some c66, some c152, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c622, c168, c66, c152] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c167, some c177, some c155, some c161, some c295, some c318, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c622, c167, c177, c155, c161, c295, c318] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c792, some c795, some c8, some c89, some c796, some c62, some c362, some c313, some c82, some c92, some c797, some c309, some c91, some c798, some c14, some c175, some c152, some c161, some c25, some c318, some c219, some c225, some c295, some c206, some c307, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c773, c622, c792, c795, c8, c89, c796, c62, c362, c313, c82, c92, c797, c309, c91, c798, c14, c175, c152, c161, c25, c318, c219, c225, c295, c206, c307] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c795 := derived795 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c796 := derived796 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c362 := derived362 a h
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c797 := derived797 a h
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c798 := derived798 a h
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c152 := h 151 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c25 := h 24 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c225 := h 224 (by decide)
  have h24 : Entails.eval a c295 := h 294 (by decide)
  have h25 : Entails.eval a c206 := h 205 (by decide)
  have h26 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c792, some c8, some c89, some c91, some c796, some c62, some c362, some c309, some c313, some c82, some c92, some c799, some c22, some c73, some c217, some c305, some c207, some c206, some c241, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c773, c622, c792, c8, c89, c91, c796, c62, c362, c309, c313, c82, c92, c799, c22, c73, c217, c305, c207, c206, c241] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c796 := derived796 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c362 := derived362 a h
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c799 := derived799 a h
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c800, some c67, some c91, some c22, some c63, some c73, some c217, some c305, some c291, some c206, some c222, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c773, c622, c800, c67, c91, c22, c63, c73, c217, c305, c291, c206, c222] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c801, some c800, some c67, some c91, some c89, some c167, some c297, some c307, some c155, some c291, some c12, some c14, some c797, some c152, some c25, some c219, some c225, some c206, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c773, c622, c801, c800, c67, c91, c89, c167, c297, c307, c155, c291, c12, c14, c797, c152, c25, c219, c225, c206] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c801 := derived801 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c797 := derived797 a h
  have h15 : Entails.eval a c152 := h 151 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c800, some c67, some c91, some c802, some c313, some c315, some c83, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c622, c773, c800, c67, c91, c802, c313, c315, c83] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c802 := derived802 a h
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c803, some c92, some c800, some c67, some c91, some c89, some c81, some c63, some c4, some c311, some c168, some c298, some c305, some c152, some c554, some c291, some c13, some c155, some c24, some c218, some c224, some c206, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c773, c622, c803, c92, c800, c67, c91, c89, c81, c63, c4, c311, c168, c298, c305, c152, c554, c291, c13, c155, c24, c218, c224, c206] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c803 := derived803 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c800 := derived800 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c152 := h 151 (by decide)
  have h16 : Entails.eval a c554 := derived554 a h
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c155 := h 154 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  have h21 : Entails.eval a c218 := h 217 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c800, some c67, some c89, some c803, some c92, some c804, some c313, some c82, some c311, some c168, some c298, some c554, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c773, c622, c800, c67, c89, c803, c92, c804, c313, c82, c311, c168, c298, c554] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c804 := derived804 a h
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c554 := derived554 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c167, some c297, some c158, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c622, c167, c297, c158] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c297 := h 296 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c800, some c67, some c91, some c89, some c805, some c21, some c71, some c62, some c216, some c311, some c168, some c298, some c806, some c313, some c542, some c72, some c307, some c291, some c206, some c221, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c773, c622, c800, c67, c91, c89, c805, c21, c71, c62, c216, c311, c168, c298, c806, c313, c542, c72, c307, c291, c206, c221] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c805 := derived805 a h
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c806 := derived806 a h
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c542 := derived542 a h
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  have h19 : Entails.eval a c291 := h 290 (by decide)
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨15, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c800, some c67, some c91, some c89, some c81, some c311, some c542, some c298, some c807, some c4, some c180, some c63, some c307, some c155, some c291, some c573, some c13, some c15, some c152, some c717, some c21, some c206, some c221, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c622, c773, c800, c67, c91, c89, c81, c311, c542, c298, c807, c4, c180, c63, c307, c155, c291, c573, c13, c15, c152, c717, c21, c206, c221] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c542 := derived542 a h
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c807 := derived807 a h
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c573 := derived573 a h
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c152 := h 151 (by decide)
  have h21 : Entails.eval a c717 := derived717 a h
  have h22 : Entails.eval a c21 := h 20 (by decide)
  have h23 : Entails.eval a c206 := h 205 (by decide)
  have h24 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c800, some c67, some c91, some c89, some c81, some c311, some c542, some c298, some c72, some c24, some c305, some c218, some c291, some c206, some c224, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c773, c622, c800, c67, c91, c89, c81, c311, c542, c298, c72, c24, c305, c218, c291, c206, c224] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c542 := derived542 a h
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c807, some c800, some c67, some c91, some c4, some c180, some c89, some c81, some c311, some c63, some c307, some c808, some c291, some c166, some c316, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c773, c622, c807, c800, c67, c91, c4, c180, c89, c81, c311, c63, c307, c808, c291, c166, c316] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c807 := derived807 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  have h13 : Entails.eval a c808 := derived808 a h
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c800, some c810, some c297, some c809, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c622, c800, c810, c297, c809] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c810 := derived810 a h
  have h3 : Entails.eval a c297 := h 296 (by decide)
  have h4 : Entails.eval a c809 := derived809 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c179, some c12, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c180, c179, c12] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨46, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c298, some c166, some c308, some c318, some c291, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c622, c298, c166, c308, c318, c291] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c800, some c67, some c89, some c91, some c807, some c812, some c811, some c313, some c297, some c813, some c311, some c62, some c82, some c92, some c801, some c14, some c307, some c155, some c291, some c165, some c318, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c773, c622, c800, c67, c89, c91, c807, c812, c811, c313, c297, c813, c311, c62, c82, c92, c801, c14, c307, c155, c291, c165, c318] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c812 := derived812 a h
  have h8 : Entails.eval a c811 := derived811 a h
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c813 := derived813 a h
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c801 := derived801 a h
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  have h19 : Entails.eval a c155 := h 154 (by decide)
  have h20 : Entails.eval a c291 := h 290 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c814, some c800, some c811, some c313, some c297, some c67, some c91, some c89, some c311, some c3, some c62, some c82, some c152, some c92, some c73, some c25, some c307, some c219, some c291, some c206, some c225, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c773, c622, c814, c800, c811, c313, c297, c67, c91, c89, c311, c3, c62, c82, c152, c92, c73, c25, c307, c219, c291, c206, c225] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c814 := derived814 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c811 := derived811 a h
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  have h19 : Entails.eval a c219 := h 218 (by decide)
  have h20 : Entails.eval a c291 := h 290 (by decide)
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c800, some c67, some c89, some c91, some c807, some c811, some c313, some c297, some c812, some c814, some c815, some c298, some c158, some c308, some c165, some c291, some c318, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c622, c773, c800, c67, c89, c91, c807, c811, c313, c297, c812, c814, c815, c298, c158, c308, c165, c291, c318] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c811 := derived811 a h
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c297 := h 296 (by decide)
  have h10 : Entails.eval a c812 := derived812 a h
  have h11 : Entails.eval a c814 := derived814 a h
  have h12 : Entails.eval a c815 := derived815 a h
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c816, some c729, some c774, some c407, some c71, some c542, some c675, some c313, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c773, c816, c729, c774, c407, c71, c542, c675, c313] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c816 := derived816 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c407 := derived407 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c542 := derived542 a h
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c622, some c816, some c774, some c729, some c817, some c91, some c90, some c536, some c86, some c72, some c313, some c303, some c294, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c773, c622, c816, c774, c729, c817, c91, c90, c536, c86, c72, c313, c303, c294] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c816 := derived816 a h
  have h3 : Entails.eval a c774 := derived774 a h
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c817 := derived817 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c536 := derived536 a h
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c303 := h 302 (by decide)
  have h13 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c816, some c818, some c315, some c675, some c311, some c62, some c82, some c299, some c90, some c92, some c73, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c773, c816, c818, c315, c675, c311, c62, c82, c299, c90, c92, c73] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c816 := derived816 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c675 := derived675 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c773, some c816, some c818, some c315, some c311, some c675, some c819, some c89, some c88, some c86, some c431, some c90, some c293, some c73, some c303, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c622, c773, c816, c818, c315, c311, c675, c819, c89, c88, c86, c431, c90, c293, c73, c303] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c773 := derived773 a h
  have h2 : Entails.eval a c816 := derived816 a h
  have h3 : Entails.eval a c818 := derived818 a h
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c675 := derived675 a h
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c431 := derived431 a h
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c773, some c447, some c39, some c118, some c49, some c51, some c137, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c773, c447, c39, c118, c49, c51, c137] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c773 := derived773 a h
  have h1 : Entails.eval a c447 := derived447 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c178, some c175, some c821, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c178, c175, c821] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c178 := h 177 (by decide)
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c821 := derived821 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived822

end CochromaticTwenty.Certificates.B16_2_1
