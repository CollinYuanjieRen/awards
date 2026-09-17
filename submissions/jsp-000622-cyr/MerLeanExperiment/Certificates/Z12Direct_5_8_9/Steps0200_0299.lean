import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_8_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c758 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c755, some c757, some c47, some c118, some c8, some c129, some c212, some c27, some c200, some c355, some c467, some c327, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p758 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 31) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c752, c755, c757, c47, c118, c8, c129, c212, c27, c200, c355, c467, c327] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c755 := derived755 a h
  have h2 : Entails.eval a c757 := derived757 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c467 := h 466 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c756, some c758, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p759 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 31) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c756, c758] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c756 := derived756 a h
  have h1 : Entails.eval a c758 := derived758 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c760 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c201, some c212, some c609, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p760 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 31) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c201, c212, c609] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c609 := derived609 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c759, some c73, some c760, some c212, some c607, some c507, some c485, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p761 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 31) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c681, c759, c73, c760, c212, c607, c507, c485] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c760 := derived760 a h
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c607 := derived607 a h
  have h6 : Entails.eval a c507 := h 506 (by decide)
  have h7 : Entails.eval a c485 := h 484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c761, some c200, some c247, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p762 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 31) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c761, c200, c247] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c761 := derived761 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c759, some c73, some c75, some c74, some c762, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p763 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 31) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c681, c759, c73, c75, c74, c762] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c762 := derived762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c763, some c158, some c251, some c75, some c212, some c38, some c200, some c278, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p764 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 31) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c681, c763, c158, c251, c75, c212, c38, c200, c278] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c251, some c10, some c212, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p765 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 31) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c251, c10, c212] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c251 := h 250 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c23, some c184, some c270, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p766 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 31) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c681, c23, c184, c270] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c759, some c764, some c765, some c73, some c212, some c754, some c766, some c419, some c453, some c69, some c267, some c329, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p767 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 31) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c681, c752, c759, c764, c765, c73, c212, c754, c766, c419, c453, c69, c267, c329] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c764 := derived764 a h
  have h4 : Entails.eval a c765 := derived765 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c754 := derived754 a h
  have h8 : Entails.eval a c766 := derived766 a h
  have h9 : Entails.eval a c419 := h 418 (by decide)
  have h10 : Entails.eval a c453 := h 452 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c759, some c764, some c767, some c253, some c206, some c241, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p768 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 31) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c759, c764, c767, c253, c206, c241] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c759 := derived759 a h
  have h1 : Entails.eval a c764 := derived764 a h
  have h2 : Entails.eval a c767 := derived767 a h
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c768, some c6, some c250, some c4, some c208, some c377, some c153, some c371, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p769 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 31) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c752, c681, c768, c6, c250, c4, c208, c377, c153, c371] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c768 := derived768 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c769, some c271, some c4, some c205, some c245, some c252, some c120, some c46, some c165, some c241, some c278, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p770 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 31) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c681, c769, c271, c4, c205, c245, c252, c120, c46, c165, c241, c278] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c770, some c769, some c271, some c10, some c253, some c241, some c119, some c120, some c118, some c88, some c136, some c45, some c386, some c343, some c400, some c480, some c286, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p771 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 31) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c752, c681, c770, c769, c271, c10, c253, c241, c119, c120, c118, c88, c136, c45, c386, c343, c400, c480, c286] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c770 := derived770 a h
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c271 := h 270 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c386 := h 385 (by decide)
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c400 := h 399 (by decide)
  have h17 : Entails.eval a c480 := h 479 (by decide)
  have h18 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c120, some c118, some c88, some c79, some c165, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p772 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 31) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c681, c120, c118, c88, c79, c165] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c769, some c271, some c770, some c771, some c772, some c73, some c165, some c212, some c84, some c226, some c29, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p773 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 31) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c681, c769, c271, c770, c771, c772, c73, c165, c212, c84, c226, c29] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c771 := derived771 a h
  have h5 : Entails.eval a c772 := derived772 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c769, some c271, some c770, some c771, some c772, some c73, some c165, some c119, some c212, some c773, some c89, some c34, some c43, some c90, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p774 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 31) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c681, c769, c271, c770, c771, c772, c73, c165, c119, c212, c773, c89, c34, c43, c90] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c771 := derived771 a h
  have h5 : Entails.eval a c772 := derived772 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c773 := derived773 a h
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c165, some c67, some c433, some c377, some c463, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p775 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 31) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c752, c681, c165, c67, c433, c377, c463] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c433 := h 432 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c463 := h 462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c769, some c271, some c770, some c771, some c772, some c119, some c165, some c73, some c774, some c118, some c760, some c775, some c16, some c91, some c182, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p776 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 31) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c681, c769, c271, c770, c771, c772, c119, c165, c73, c774, c118, c760, c775, c16, c91, c182] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c771 := derived771 a h
  have h5 : Entails.eval a c772 := derived772 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c774 := derived774 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c760 := derived760 a h
  have h12 : Entails.eval a c775 := derived775 a h
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c769, some c271, some c776, some c244, some c252, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p777 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 31) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c769, c271, c776, c244, c252] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c769 := derived769 a h
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c776 := derived776 a h
  have h3 : Entails.eval a c244 := h 243 (by decide)
  have h4 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c158, some c777, some c10, some c108, some c13, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p778 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 31) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c681, c158, c777, c10, c108, c13] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨29, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c205, some c118, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p779 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 31) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c205, c118] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c780 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c158, some c778, some c75, some c779, some c777, some c251, some c417, some c521, some c215, some c283, some c40, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p780 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 31) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c681, c752, c158, c778, c75, c779, c777, c251, c417, c521, c215, c283, c40] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c778 := derived778 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c779 := derived779 a h
  have h6 : Entails.eval a c777 := derived777 a h
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c417 := h 416 (by decide)
  have h9 : Entails.eval a c521 := h 520 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c778, some c158, some c75, some c74, some c780, some c212, some c278, some c200, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p781 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 31) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c681, c778, c158, c75, c74, c780, c212, c278, c200] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c778 := derived778 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c780 := derived780 a h
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c158, some c778, some c781, some c246, some c201, some c166, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p782 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 31) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c681, c158, c778, c781, c246, c201, c166] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c781 := derived781 a h
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c205, some c782, some c777, some c19, some c229, some c165, some c245, some c404, some c513, some c168, some c280, some c48, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p783 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 31) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c681, c752, c205, c782, c777, c19, c229, c165, c245, c404, c513, c168, c280, c48] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c782 := derived782 a h
  have h4 : Entails.eval a c777 := derived777 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c229 := h 228 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c404 := h 403 (by decide)
  have h10 : Entails.eval a c513 := h 512 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c205, some c783, some c6, some c242, some c39, some c279, some c201, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p784 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 31) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c681, c205, c783, c6, c242, c39, c279, c201] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c783 := derived783 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c242 := h 241 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c279 := h 278 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c777, some c782, some c784, some c272, some c279, some c242, some c11, some c47, some c241, some c253, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p785 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 31) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c752, c777, c782, c784, c272, c279, c242, c11, c47, c241, c253] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c782 := derived782 a h
  have h3 : Entails.eval a c784 := derived784 a h
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c279 := h 278 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c777, some c782, some c784, some c272, some c785, some c201, some c73, some c17, some c200, some c247, some c27, some c120, some c241, some c11, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p786 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 31) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c752, c681, c777, c782, c784, c272, c785, c201, c73, c17, c200, c247, c27, c120, c241, c11] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c782 := derived782 a h
  have h4 : Entails.eval a c784 := derived784 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c785 := derived785 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c786, some c158, some c73, some c116, some c645, some c242, some c17, some c11, some c423, some c76, some c241, some c365, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p787 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 31) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c752, c681, c786, c158, c73, c116, c645, c242, c17, c11, c423, c76, c241, c365] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c242 := h 241 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c423 := h 422 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c787, some c201, some c279, some c242, some c786, some c241, some c117, some c278, some c78, some c114, some c692, some c200, some c373, some c434, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p788 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 31) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c752, c787, c201, c279, c242, c786, c241, c117, c278, c78, c114, c692, c200, c373, c434] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c242 := h 241 (by decide)
  have h5 : Entails.eval a c786 := derived786 a h
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c692 := derived692 a h
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c434 := h 433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c786, some c787, some c201, some c279, some c242, some c788, some c11, some c225, some c203, some c119, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p789 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 31) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c752, c681, c786, c787, c201, c279, c242, c788, c11, c225, c203, c119] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c279 := h 278 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c788 := derived788 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c786, some c225, some c119, some c77, some c203, some c252, some c475, some c523, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p790 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 31) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c681, c752, c786, c225, c119, c77, c203, c252, c475, c523] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c475 := h 474 (by decide)
  have h9 : Entails.eval a c523 := h 522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c786, some c225, some c271, some c91, some c50, some c185, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p791 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 31) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c681, c786, c225, c271, c91, c50, c185] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c789, some c786, some c225, some c271, some c790, some c117, some c78, some c165, some c88, some c791, some c89, some c356, some c228, some c377, some c508, some c539, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p792 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 31) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c681, c752, c789, c786, c225, c271, c790, c117, c78, c165, c88, c791, c89, c356, c228, c377, c508, c539] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c786 := derived786 a h
  have h4 : Entails.eval a c225 := h 224 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c790 := derived790 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c791 := derived791 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c508 := h 507 (by decide)
  have h17 : Entails.eval a c539 := h 538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c117, some c78, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p793 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 31) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c117, c78] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c794 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨14, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c416, some c520, some c131, some c479, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p794 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 31) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c681, c752, c416, c520, c131, c479] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c416 := h 415 (by decide)
  have h3 : Entails.eval a c520 := h 519 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c479 := h 478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c522, some c418, some c69, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p795 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 31) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c752, c522, c418, c69] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c522 := h 521 (by decide)
  have h2 : Entails.eval a c418 := h 417 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c786, some c119, some c794, some c113, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p796 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 31) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c681, c786, c119, c794, c113] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c794 := derived794 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c789, some c786, some c792, some c272, some c793, some c166, some c186, some c11, some c108, some c795, some c796, some c120, some c113, some c76, some c416, some c378, some c42, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p797 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 31) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c752, c681, c789, c786, c792, c272, c793, c166, c186, c11, c108, c795, c796, c120, c113, c76, c416, c378, c42] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c786 := derived786 a h
  have h4 : Entails.eval a c792 := derived792 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c793 := derived793 a h
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c795 := derived795 a h
  have h12 : Entails.eval a c796 := derived796 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c416 := h 415 (by decide)
  have h17 : Entails.eval a c378 := h 377 (by decide)
  have h18 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c786, some c789, some c797, some c158, some c19, some c73, some c645, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p798 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 31) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c681, c786, c789, c797, c158, c19, c73, c645] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c645 := derived645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c204, some c208, some c119, some c112, some c77, some c120, some c246, some c45, some c245, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p799 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 31) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c681, c752, c204, c208, c119, c112, c77, c120, c246, c45, c245] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c786, some c798, some c799, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p800 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 31) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c786, c798, c799] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c786 := derived786 a h
  have h1 : Entails.eval a c798 := derived798 a h
  have h2 : Entails.eval a c799 := derived799 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c591, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p801 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 31) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c88, c591] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c802 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c800, some c260, some c107, some c165, some c254, some c557, some c455, some c274, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p802 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 31) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c752, c681, c800, c260, c107, c165, c254, c557, c455, c274] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c254 := h 253 (by decide)
  have h7 : Entails.eval a c557 := h 556 (by decide)
  have h8 : Entails.eval a c455 := h 454 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c681, some c219, some c260, some c77, some c120, some c801, some c45, some c802, some c161, some c18, some c165, some c160, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p803 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 31) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c800, c752, c681, c219, c260, c77, c120, c801, c45, c802, c161, c18, c165, c160] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c801 := derived801 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c802 := derived802 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c681, some c752, some c260, some c211, some c254, some c119, some c802, some c165, some c161, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p804 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 31) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c800, c681, c752, c260, c211, c254, c119, c802, c165, c161] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c802 := derived802 a h
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c681, some c219, some c260, some c803, some c211, some c254, some c119, some c591, some c78, some c715, some c69, some c100, some c191, some c134, some c281, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p805 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 31) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c752, c800, c681, c219, c260, c803, c211, c254, c119, c591, c78, c715, c69, c100, c191, c134, c281] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c591 := derived591 a h
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c715 := derived715 a h
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c681, some c219, some c260, some c803, some c211, some c254, some c805, some c165, some c804, some c166, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p806 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 31) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c752, c800, c681, c219, c260, c803, c211, c254, c805, c165, c804, c166] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c805 := derived805 a h
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c804 := derived804 a h
  have h11 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c681, some c219, some c260, some c806, some c112, some c39, some c73, some c244, some c162, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p807 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 31) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c800, c752, c681, c219, c260, c806, c112, c39, c73, c244, c162] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c806 := derived806 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c800, some c752, some c807, some c219, some c260, some c119, some c211, some c117, some c793, some c73, some c160, some c165, some c272, some c715, some c397, some c141, some c539, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p808 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 31) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c681, c800, c752, c807, c219, c260, c119, c211, c117, c793, c73, c160, c165, c272, c715, c397, c141, c539] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c807 := derived807 a h
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c211 := h 210 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c793 := derived793 a h
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c715 := derived715 a h
  have h15 : Entails.eval a c397 := h 396 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  have h17 : Entails.eval a c539 := h 538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c800, some c752, some c219, some c808, some c120, some c807, some c260, some c272, some c11, some c160, some c117, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p809 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 31) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c681, c800, c752, c219, c808, c120, c807, c260, c272, c11, c160, c117] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨26, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c808, some c77, some c807, some c219, some c136, some c117, some c795, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p810 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 31) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c752, c800, c808, c77, c807, c219, c136, c117, c795] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c808 := derived808 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c807 := derived807 a h
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c795 := derived795 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c800, some c752, some c219, some c808, some c120, some c807, some c810, some c203, some c11, some c809, some c793, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p811 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 31) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c681, c800, c752, c219, c808, c120, c807, c810, c203, c11, c809, c793] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c810 := derived810 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c809 := derived809 a h
  have h11 : Entails.eval a c793 := derived793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c681, some c219, some c260, some c807, some c808, some c120, some c811, some c116, some c645, some c17, some c19, some c11, some c162, some c527, some c474, some c41, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p812 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 31) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c800, c752, c681, c219, c260, c807, c808, c120, c811, c116, c645, c17, c19, c11, c162, c527, c474, c41] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c807 := derived807 a h
  have h6 : Entails.eval a c808 := derived808 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c811 := derived811 a h
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c645 := derived645 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c162 := h 161 (by decide)
  have h15 : Entails.eval a c527 := h 526 (by decide)
  have h16 : Entails.eval a c474 := h 473 (by decide)
  have h17 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c800, some c752, some c215, some c221, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p813 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 31) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c812, c800, c752, c215, c221] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c800, some c752, some c214, some c220, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p814 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 31) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c812, c800, c752, c214, c220] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c813, some c814, some c67, some c66, some c11, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p815 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 31) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c752, c813, c814, c67, c66, c11] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c814 := derived814 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c681, some c752, some c800, some c67, some c127, some c118, some c79, some c129, some c87, some c260, some c88, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p816 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 31) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c812, c681, c752, c800, c67, c127, c118, c79, c129, c87, c260, c88] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c129 := h 128 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c812, some c681, some c815, some c220, some c144, some c476, some c345, some c302, some c461, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p817 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 31) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c800, c752, c812, c681, c815, c220, c144, c476, c345, c302, c461] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c681 := derived681 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c476 := h 475 (by decide)
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  have h10 : Entails.eval a c461 := h 460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c812, some c681, some c815, some c817, some c816, some c221, some c362, some c177, some c303, some c300, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p818 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 31) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c800, c752, c812, c681, c815, c817, c816, c221, c362, c177, c303, c300] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c681 := derived681 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c817 := derived817 a h
  have h6 : Entails.eval a c816 := derived816 a h
  have h7 : Entails.eval a c221 := h 220 (by decide)
  have h8 : Entails.eval a c362 := h 361 (by decide)
  have h9 : Entails.eval a c177 := h 176 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c812, some c681, some c800, some c815, some c221, some c149, some c463, some c414, some c140, some c60, some c2, some c190, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p819 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 31) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c752, c812, c681, c800, c815, c221, c149, c463, c414, c140, c60, c2, c190] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c463 := h 462 (by decide)
  have h8 : Entails.eval a c414 := h 413 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c681, some c800, some c752, some c369, some c43, some c451, some c207, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p820 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 31) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c812, c681, c800, c752, c369, c43, c451, c207] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c752 := derived752 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c451 := h 450 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c812, some c818, some c815, some c221, some c149, some c414, some c463, some c819, some c220, some c820, some c344, some c143, some c68, some c360, some c486, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p821 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 31) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c800, c752, c812, c818, c815, c221, c149, c414, c463, c819, c220, c820, c344, c143, c68, c360, c486] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c818 := derived818 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c414 := h 413 (by decide)
  have h8 : Entails.eval a c463 := h 462 (by decide)
  have h9 : Entails.eval a c819 := derived819 a h
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c820 := derived820 a h
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c486 := h 485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c812, some c681, some c800, some c815, some c818, some c821, some c816, some c147, some c220, some c3, some c144, some c519, some c324, some c59, some c194, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p822 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 31) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c752, c812, c681, c800, c815, c818, c821, c816, c147, c220, c3, c144, c519, c324, c59, c194] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c800 := derived800 a h
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c818 := derived818 a h
  have h6 : Entails.eval a c821 := derived821 a h
  have h7 : Entails.eval a c816 := derived816 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c220 := h 219 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c519 := h 518 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c552, some c469, some c518, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p823 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 31) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c800, c752, c552, c469, c518] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c552 := h 551 (by decide)
  have h3 : Entails.eval a c469 := h 468 (by decide)
  have h4 : Entails.eval a c518 := h 517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c681, some c812, some c823, some c176, some c310, some c314, some c25, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p824 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 31) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c800, c752, c681, c812, c823, c176, c310, c314, c25] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c812 := derived812 a h
  have h4 : Entails.eval a c823 := derived823 a h
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c681, some c752, some c812, some c822, some c39, some c816, some c450, some c824, some c19, some c214, some c207, some c333, some c308, some c118, some c11, some c79, some c331, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p825 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 31) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c800, c681, c752, c812, c822, c39, c816, c450, c824, c19, c214, c207, c333, c308, c118, c11, c79, c331] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c812 := derived812 a h
  have h4 : Entails.eval a c822 := derived822 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c816 := derived816 a h
  have h7 : Entails.eval a c450 := h 449 (by decide)
  have h8 : Entails.eval a c824 := derived824 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c681, some c752, some c812, some c822, some c825, some c553, some c177, some c450, some c39, some c19, some c215, some c207, some c334, some c306, some c118, some c11, some c79, some c328, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p826 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 31) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c800, c681, c752, c812, c822, c825, c553, c177, c450, c39, c19, c215, c207, c334, c306, c118, c11, c79, c328] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c812 := derived812 a h
  have h4 : Entails.eval a c822 := derived822 a h
  have h5 : Entails.eval a c825 := derived825 a h
  have h6 : Entails.eval a c553 := h 552 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c450 := h 449 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c79 := h 78 (by decide)
  have h18 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c812, some c237, some c224, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p827 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 31) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c800, c812, c237, c224] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c681, some c177, some c140, some c471, some c44, some c309, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p828 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 31) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c752, c800, c681, c177, c140, c471, c44, c309] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c471 := h 470 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c800, some c812, some c752, some c822, some c39, some c825, some c553, some c177, some c450, some c826, some c827, some c129, some c828, some c293, some c332, some c456, some c347, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p829 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 31) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c681, c800, c812, c752, c822, c39, c825, c553, c177, c450, c826, c827, c129, c828, c293, c332, c456, c347] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c752 := derived752 a h
  have h4 : Entails.eval a c822 := derived822 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c825 := derived825 a h
  have h7 : Entails.eval a c553 := h 552 (by decide)
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c450 := h 449 (by decide)
  have h10 : Entails.eval a c826 := derived826 a h
  have h11 : Entails.eval a c827 := derived827 a h
  have h12 : Entails.eval a c129 := h 128 (by decide)
  have h13 : Entails.eval a c828 := derived828 a h
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c332 := h 331 (by decide)
  have h16 : Entails.eval a c456 := h 455 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c681, some c752, some c448, some c361, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p830 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 31) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c800, c681, c752, c448, c361] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c448 := h 447 (by decide)
  have h4 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c830, some c421, some c449, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p831 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 31) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c752, c800, c830, c421, c449] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c830 := derived830 a h
  have h3 : Entails.eval a c421 := h 420 (by decide)
  have h4 : Entails.eval a c449 := h 448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c812, some c466, some c305, some c69, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p832 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 31) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c681, c812, c466, c305, c69] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c466 := h 465 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c827, some c829, some c831, some c34, some c832, some c448, some c440, some c692, some c820, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p833 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 31) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c752, c800, c827, c829, c831, c34, c832, c448, c440, c692, c820] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c827 := derived827 a h
  have h3 : Entails.eval a c829 := derived829 a h
  have h4 : Entails.eval a c831 := derived831 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c832 := derived832 a h
  have h7 : Entails.eval a c448 := h 447 (by decide)
  have h8 : Entails.eval a c440 := h 439 (by decide)
  have h9 : Entails.eval a c692 := derived692 a h
  have h10 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨19, by decide⟩, false), (⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c752, some c800, some c371, some c557, some c455, some c25, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p834 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 31) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c812, c752, c800, c371, c557, c455, c25] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c557 := h 556 (by decide)
  have h5 : Entails.eval a c455 := h 454 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨22, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c834, some c466, some c354, some c69, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p835 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 31) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c681, c834, c466, c354, c69] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c466 := h 465 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c525, some c421, some c44, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p836 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 31) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c752, c525, c421, c44] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c525 := h 524 (by decide)
  have h2 : Entails.eval a c421 := h 420 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c752, some c829, some c827, some c833, some c835, some c836, some c361, some c475, some c69, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p837 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 31) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c681, c752, c829, c827, c833, c835, c836, c361, c475, c69] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c829 := derived829 a h
  have h3 : Entails.eval a c827 := derived827 a h
  have h4 : Entails.eval a c833 := derived833 a h
  have h5 : Entails.eval a c835 := derived835 a h
  have h6 : Entails.eval a c836 := derived836 a h
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c475 := h 474 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c681, some c812, some c837, some c221, some c42, some c300, some c305, some c820, some c510, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p838 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 31) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c752, c800, c681, c812, c837, c221, c42, c300, c305, c820, c510] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c812 := derived812 a h
  have h4 : Entails.eval a c837 := derived837 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c820 := derived820 a h
  have h10 : Entails.eval a c510 := h 509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c800, some c812, some c829, some c837, some c221, some c838, some c69, some c303, some c301, some c63, some c31, some c293, some c79, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p839 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 31) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c752, c681, c800, c812, c829, c837, c221, c838, c69, c303, c301, c63, c31, c293, c79] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c812 := derived812 a h
  have h4 : Entails.eval a c829 := derived829 a h
  have h5 : Entails.eval a c837 := derived837 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c838 := derived838 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c812, some c839, some c215, some c829, some c69, some c128, some c123, some c124, some c125, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p840 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 31) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c752, c681, c812, c839, c215, c829, c69, c128, c123, c124, c125] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c839 := derived839 a h
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c829 := derived829 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c64, some c75, some c160, some c13, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p841 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 31) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c812, c64, c75, c160, c13] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c681, some c812, some c829, some c839, some c815, some c840, some c841, some c118, some c548, some c121, some c120, some c207, some c472, some c15, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p842 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 31) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c752, c681, c812, c829, c839, c815, c840, c841, c118, c548, c121, c120, c207, c472, c15] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c812 := derived812 a h
  have h3 : Entails.eval a c829 := derived829 a h
  have h4 : Entails.eval a c839 := derived839 a h
  have h5 : Entails.eval a c815 := derived815 a h
  have h6 : Entails.eval a c840 := derived840 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c548 := h 547 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c472 := h 471 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c681, some c842, some c829, some c120, some c207, some c67, some c62, some c212, some c16, some c21, some c231, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p843 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 31) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c812, c681, c842, c829, c120, c207, c67, c62, c212, c16, c21, c231] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c681 := derived681 a h
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c829 := derived829 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c812, some c829, some c843, some c118, some c79, some c75, some c160, some c165, some c88, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p844 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 31) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c681, c812, c829, c843, c118, c79, c75, c160, c165, c88] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c812 := derived812 a h
  have h2 : Entails.eval a c829 := derived829 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c11, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p845 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 31) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c752, c11] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c846 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c752, some c12, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p846 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 31) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c800, c752, c12] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c752 := derived752 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c14, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p847 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 31) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c800, c14] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c848 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c17, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p848 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 31) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c752, c17] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c849 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c752, some c800, some c18, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p849 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 31) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c752, c800, c18] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c752 := derived752 a h
  have h1 : Entails.eval a c800 := derived800 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c19, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p850 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 31) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c681, c19] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c851 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c800, some c20, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p851 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 31) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c800, c20] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c852 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c43, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p852 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 31) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c681, c43] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c853 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c73, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p853 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 31) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c681, c73] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c854 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c75, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p854 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 31) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c812, c75] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c855 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨22, by decide⟩, true), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c812, some c84, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p855 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 31) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c812, c84] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c812 := derived812 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c856 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c112, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p856 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 31) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c681, c112] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c857 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c681, some c120, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p857 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 31) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c681, c120] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived857

end CochromaticTwenty.Certificates.Z12Direct_5_8_9
