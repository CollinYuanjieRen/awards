import MerLeanExperiment.Certificates.B16_2_2.Steps0300_0399

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c784 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨47, by decide⟩, true), (⟨11, by decide⟩, false), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c17, some c19, some c169, some c88, some c105, some c112, some c94, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c109, c110, c17, c19, c169, c88, c105, c112, c94] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨50, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c171, some c784, some c98, some c6, some c78, some c108, some c162, some c356, some c73, some c509, some c372, some c107, some c88, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c191, c171, c784, c98, c6, c78, c108, c162, c356, c73, c509, c372, c107, c88] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c784 := derived784 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c509 := derived509 a h
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨43, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c589, some c182, some c3, some c743, some c376, some c543, some c162, some c356, some c443, some c73, some c509, some c372, some c107, some c24, some c88, some c252, some c375, some c239, some c25, some c256, some c742, some c203, some c308, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c383, c589, c182, c3, c743, c376, c543, c162, c356, c443, c73, c509, c372, c107, c24, c88, c252, c375, c239, c25, c256, c742, c203, c308] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c743 := derived743 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c443 := derived443 a h
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c509 := derived509 a h
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c375 := h 374 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c25 := h 24 (by decide)
  have h20 : Entails.eval a c256 := h 255 (by decide)
  have h21 : Entails.eval a c742 := derived742 a h
  have h22 : Entails.eval a c203 := h 202 (by decide)
  have h23 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c753, some c781, some c177, some c191, some c783, some c589, some c743, some c782, some c785, some c3, some c182, some c108, some c786, some c78, some c110, some c17, some c19, some c112, some c742, some c308, some c203, some c254, some c256, some c522, some c125, some c238, some c374, some c375, some c88, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c376, c383, c737, c753, c781, c177, c191, c783, c589, c743, c782, c785, c3, c182, c108, c786, c78, c110, c17, c19, c112, c742, c308, c203, c254, c256, c522, c125, c238, c374, c375, c88] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c781 := derived781 a h
  have h5 : Entails.eval a c177 := h 176 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c783 := derived783 a h
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c743 := derived743 a h
  have h10 : Entails.eval a c782 := derived782 a h
  have h11 : Entails.eval a c785 := derived785 a h
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c786 := derived786 a h
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c112 := h 111 (by decide)
  have h21 : Entails.eval a c742 := derived742 a h
  have h22 : Entails.eval a c308 := h 307 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c254 := h 253 (by decide)
  have h25 : Entails.eval a c256 := h 255 (by decide)
  have h26 : Entails.eval a c522 := derived522 a h
  have h27 : Entails.eval a c125 := h 124 (by decide)
  have h28 : Entails.eval a c238 := h 237 (by decide)
  have h29 : Entails.eval a c374 := h 373 (by decide)
  have h30 : Entails.eval a c375 := h 374 (by decide)
  have h31 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c742, some c300, some c130, some c339, some c159, some c155, some c66, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c3, c742, c300, c130, c339, c159, c155, c66] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c742 := derived742 a h
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c44, some c140, some c206, some c50, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c300, c44, c140, c206, c50] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c5, some c191, some c788, some c171, some c589, some c186, some c378, some c111, some c112, some c740, some c88, some c27, some c784, some c169, some c115, some c123, some c256, some c78, some c17, some c162, some c73, some c789, some c147, some c211, some c50, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c787, c180, c5, c191, c788, c171, c589, c186, c378, c111, c112, c740, c88, c27, c784, c169, c115, c123, c256, c78, c17, c162, c73, c789, c147, c211, c50] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c788 := derived788 a h
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c589 := derived589 a h
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c740 := derived740 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c784 := derived784 a h
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c256 := h 255 (by decide)
  have h19 : Entails.eval a c78 := h 77 (by decide)
  have h20 : Entails.eval a c17 := h 16 (by decide)
  have h21 : Entails.eval a c162 := h 161 (by decide)
  have h22 : Entails.eval a c73 := h 72 (by decide)
  have h23 : Entails.eval a c789 := derived789 a h
  have h24 : Entails.eval a c147 := h 146 (by decide)
  have h25 : Entails.eval a c211 := h 210 (by decide)
  have h26 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c589, some c787, some c5, some c180, some c191, some c788, some c171, some c790, some c739, some c98, some c784, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c378, c589, c787, c5, c180, c191, c788, c171, c790, c739, c98, c784] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c788 := derived788 a h
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c790 := derived790 a h
  have h9 : Entails.eval a c739 := derived739 a h
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c784 := derived784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c791, some c178, some c171, some c589, some c787, some c5, some c180, some c739, some c98, some c784, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c378, c791, c178, c171, c589, c787, c5, c180, c739, c98, c784] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c791 := derived791 a h
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c787 := derived787 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c739 := derived739 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c784 := derived784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c211, some c50, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c147, c211, c50] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c791, some c178, some c171, some c787, some c5, some c1, some c105, some c27, some c256, some c123, some c180, some c792, some c111, some c88, some c169, some c17, some c793, some c300, some c44, some c137, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c378, c791, c178, c171, c787, c5, c1, c105, c27, c256, c123, c180, c792, c111, c88, c169, c17, c793, c300, c44, c137] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c791 := derived791 a h
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c787 := derived787 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c792 := derived792 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c793 := derived793 a h
  have h18 : Entails.eval a c300 := h 299 (by decide)
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c5, some c105, some c27, some c123, some c186, some c180, some c111, some c740, some c88, some c374, some c365, some c175, some c28, some c239, some c257, some c789, some c204, some c211, some c64, some c45, some c130, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c171, c5, c105, c27, c123, c186, c180, c111, c740, c88, c374, c365, c175, c28, c239, c257, c789, c204, c211, c64, c45, c130] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c740 := derived740 a h
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c365 := h 364 (by decide)
  have h12 : Entails.eval a c175 := h 174 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c239 := h 238 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c789 := derived789 a h
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c211 := h 210 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c589, some c787, some c5, some c180, some c791, some c178, some c1, some c171, some c105, some c27, some c123, some c256, some c794, some c795, some c739, some c98, some c35, some c110, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c378, c589, c787, c5, c180, c791, c178, c1, c171, c105, c27, c123, c256, c794, c795, c739, c98, c35, c110] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c791 := derived791 a h
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c794 := derived794 a h
  have h14 : Entails.eval a c795 := derived795 a h
  have h15 : Entails.eval a c739 := derived739 a h
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c16, some c169, some c89, some c88, some c175, some c375, some c365, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c109, c110, c16, c169, c89, c88, c175, c375, c365] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c796, some c787, some c589, some c186, some c378, some c5, some c180, some c190, some c1, some c105, some c13, some c797, some c98, some c726, some c111, some c16, some c169, some c729, some c24, some c89, some c88, some c40, some c121, some c375, some c256, some c239, some c257, some c789, some c204, some c64, some c347, some c153, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c796, c787, c589, c186, c378, c5, c180, c190, c1, c105, c13, c797, c98, c726, c111, c16, c169, c729, c24, c89, c88, c40, c121, c375, c256, c239, c257, c789, c204, c64, c347, c153] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c797 := derived797 a h
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c726 := derived726 a h
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c729 := derived729 a h
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c89 := h 88 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c40 := h 39 (by decide)
  have h22 : Entails.eval a c121 := h 120 (by decide)
  have h23 : Entails.eval a c375 := h 374 (by decide)
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c239 := h 238 (by decide)
  have h26 : Entails.eval a c257 := h 256 (by decide)
  have h27 : Entails.eval a c789 := derived789 a h
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c64 := h 63 (by decide)
  have h30 : Entails.eval a c347 := h 346 (by decide)
  have h31 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c308, some c300, some c141, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c308, c300, c141] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c308 := h 307 (by decide)
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c339, some c347, some c153, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c339, c347, c153] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c589, some c378, some c186, some c796, some c799, some c800, some c136, some c190, some c798, some c178, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c787, c180, c589, c378, c186, c796, c799, c800, c136, c190, c798, c178] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c796 := derived796 a h
  have h6 : Entails.eval a c799 := derived799 a h
  have h7 : Entails.eval a c800 := derived800 a h
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c798 := derived798 a h
  have h11 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c149, some c334, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c153, c149, c334] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c45, some c140, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c50, c45, c140] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c112, some c13, some c803, some c131, some c66, some c61, some c152, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c3, c112, c13, c803, c131, c66, c61, c152] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c803 := derived803 a h
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c112, some c16, some c13, some c169, some c803, some c88, some c271, some c326, some c61, some c153, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c111, c112, c16, c13, c169, c803, c88, c271, c326, c61, c153] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c13, some c110, some c98, some c20, some c380, some c127, some c26, some c175, some c366, some c364, some c374, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c99, c13, c110, c98, c20, c380, c127, c26, c175, c366, c364, c374] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c364 := h 363 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c127, some c175, some c26, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c127, c175, c26] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c152, some c70, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c153, c152, c70] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨34, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c98, some c380, some c768, some c62, some c273, some c52, some c46, some c140, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c110, c98, c380, c768, c62, c273, c52, c46, c140] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c768 := derived768 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c804, some c187, some c180, some c204, some c805, some c99, some c806, some c105, some c808, some c809, some c9, some c190, some c186, some c338, some c160, some c158, some c70, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c5, c804, c187, c180, c204, c805, c99, c806, c105, c808, c809, c9, c190, c186, c338, c160, c158, c70] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c804 := derived804 a h
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c805 := derived805 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c806 := derived806 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c808 := derived808 a h
  have h10 : Entails.eval a c809 := derived809 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c105, some c112, some c808, some c9, some c99, some c353, some c190, some c72, some c160, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c13, c105, c112, c808, c9, c99, c353, c190, c72, c160] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c808 := derived808 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c64, some c110, some c153, some c152, some c808, some c20, some c348, some c190, some c149, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c64, c110, c153, c152, c808, c20, c348, c190, c149] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c804, some c187, some c180, some c811, some c812, some c99, some c80, some c111, some c112, some c761, some c380, some c186, some c726, some c797, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c5, c804, c187, c180, c811, c812, c99, c80, c111, c112, c761, c380, c186, c726, c797] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c804 := derived804 a h
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c811 := derived811 a h
  have h5 : Entails.eval a c812 := derived812 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c761 := derived761 a h
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c726 := derived726 a h
  have h14 : Entails.eval a c797 := derived797 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c5, some c111, some c112, some c16, some c761, some c169, some c380, some c88, some c186, some c375, some c797, some c366, some c726, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c187, c5, c111, c112, c16, c761, c169, c380, c88, c186, c375, c797, c366, c726] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c797 := derived797 a h
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c813, some c810, some c5, some c804, some c187, some c180, some c814, some c99, some c110, some c48, some c140, some c141, some c309, some c54, some c137, some c20, some c190, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c813, c810, c5, c804, c187, c180, c814, c99, c110, c48, c140, c141, c309, c54, c137, c20, c190] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c810 := derived810 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c804 := derived804 a h
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c814 := derived814 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c54 := h 53 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c5, some c180, some c813, some c810, some c815, some c13, some c105, some c112, some c9, some c99, some c190, some c56, some c186, some c141, some c148, some c299, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c187, c5, c180, c813, c810, c815, c13, c105, c112, c9, c99, c190, c56, c186, c141, c148, c299] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c810 := derived810 a h
  have h5 : Entails.eval a c815 := derived815 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c99, some c171, some c106, some c738, some c85, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c3, c99, c171, c106, c738, c85] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c738 := derived738 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c748, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c92, c748] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c748 := derived748 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c176, some c366, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c375, c176, c366] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c105, some c817, some c111, some c88, some c85, some c371, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c9, c105, c817, c111, c88, c85, c371] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c817 := derived817 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨45, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c186, some c365, some c175, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c186, c365, c175] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c186 := h 185 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c803, some c131, some c66, some c61, some c152, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c803, c131, c66, c61, c152] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c803 := derived803 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c5, some c816, some c187, some c191, some c819, some c820, some c88, some c374, some c366, some c821, some c380, some c761, some c822, some c768, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c180, c5, c816, c187, c191, c819, c820, c88, c374, c366, c821, c380, c761, c822, c768] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c816 := derived816 a h
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c819 := derived819 a h
  have h6 : Entails.eval a c820 := derived820 a h
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c374 := h 373 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c821 := derived821 a h
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c761 := derived761 a h
  have h13 : Entails.eval a c822 := derived822 a h
  have h14 : Entails.eval a c768 := derived768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨18, by decide⟩, true), (⟨46, by decide⟩, false), (⟨42, by decide⟩, true), (⟨23, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c754, some c366, some c257, some c369, some c229, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c374, c754, c366, c257, c369, c229] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c5, some c801, some c816, some c187, some c191, some c819, some c820, some c27, some c823, some c108, some c109, some c3, some c738, some c98, some c92, some c123, some c380, some c34, some c247, some c824, some c364, some c369, some c358, some c229, some c243, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c787, c180, c5, c801, c816, c187, c191, c819, c820, c27, c823, c108, c109, c3, c738, c98, c92, c123, c380, c34, c247, c824, c364, c369, c358, c229, c243] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c801 := derived801 a h
  have h4 : Entails.eval a c816 := derived816 a h
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c820 := derived820 a h
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c823 := derived823 a h
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c738 := derived738 a h
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c380 := h 379 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  have h20 : Entails.eval a c247 := h 246 (by decide)
  have h21 : Entails.eval a c824 := derived824 a h
  have h22 : Entails.eval a c364 := h 363 (by decide)
  have h23 : Entails.eval a c369 := h 368 (by decide)
  have h24 : Entails.eval a c358 := h 357 (by decide)
  have h25 : Entails.eval a c229 := h 228 (by decide)
  have h26 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c62, some c152, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c68, c62, c152] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c130, some c149, some c299, some c46, some c333, some c132, some c200, some c134, some c202, some c125, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c130, c149, c299, c46, c333, c132, c200, c134, c202, c125] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c130 := h 129 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c5, some c180, some c801, some c187, some c816, some c191, some c819, some c820, some c825, some c105, some c112, some c94, some c99, some c110, some c98, some c380, some c768, some c826, some c827, some c64, some c338, some c809, some c48, some c140, some c137, some c52, some c294, some c132, some c200, some c134, some c202, some c125, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c787, c5, c180, c801, c187, c816, c191, c819, c820, c825, c105, c112, c94, c99, c110, c98, c380, c768, c826, c827, c64, c338, c809, c48, c140, c137, c52, c294, c132, c200, c134, c202, c125] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c801 := derived801 a h
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c816 := derived816 a h
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c820 := derived820 a h
  have h9 : Entails.eval a c825 := derived825 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c768 := derived768 a h
  have h18 : Entails.eval a c826 := derived826 a h
  have h19 : Entails.eval a c827 := derived827 a h
  have h20 : Entails.eval a c64 := h 63 (by decide)
  have h21 : Entails.eval a c338 := h 337 (by decide)
  have h22 : Entails.eval a c809 := derived809 a h
  have h23 : Entails.eval a c48 := h 47 (by decide)
  have h24 : Entails.eval a c140 := h 139 (by decide)
  have h25 : Entails.eval a c137 := h 136 (by decide)
  have h26 : Entails.eval a c52 := h 51 (by decide)
  have h27 : Entails.eval a c294 := h 293 (by decide)
  have h28 : Entails.eval a c132 := h 131 (by decide)
  have h29 : Entails.eval a c200 := h 199 (by decide)
  have h30 : Entails.eval a c134 := h 133 (by decide)
  have h31 : Entails.eval a c202 := h 201 (by decide)
  have h32 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c140, some c137, some c41, some c294, some c1, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c299, c140, c137, c41, c294, c1] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, false), (⟨34, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c338, some c829, some c134, some c202, some c125, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c338, c829, c134, c202, c125] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c338 := h 337 (by decide)
  have h1 : Entails.eval a c829 := derived829 a h
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c186, some c78, some c726, some c173, some c364, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c187, c186, c78, c726, c173, c364] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c726 := derived726 a h
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨34, by decide⟩, false), (⟨36, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c336, some c379, some c5, some c831, some c338, some c829, some c830, some c270, some c200, some c297, some c52, some c140, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c180, c336, c379, c5, c831, c338, c829, c830, c270, c200, c297, c52, c140] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c831 := derived831 a h
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c829 := derived829 a h
  have h7 : Entails.eval a c830 := derived830 a h
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c46, some c140, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c52, c46, c140] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c379, some c5, some c109, some c826, some c833, some c132, some c831, some c832, some c152, some c149, some c827, some c57, some c1, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c180, c379, c5, c109, c826, c833, c132, c831, c832, c152, c149, c827, c57, c1] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c826 := derived826 a h
  have h5 : Entails.eval a c833 := derived833 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c831 := derived831 a h
  have h8 : Entails.eval a c832 := derived832 a h
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c827 := derived827 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c379, some c5, some c834, some c761, some c101, some c76, some c4, some c10, some c110, some c105, some c14, some c92, some c173, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c180, c379, c5, c834, c761, c101, c76, c4, c10, c110, c105, c14, c92, c173] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c834 := derived834 a h
  have h4 : Entails.eval a c761 := derived761 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c761, some c101, some c14, some c110, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c761, c101, c14, c110] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c761 := derived761 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c180, some c379, some c5, some c835, some c191, some c190, some c186, some c836, some c109, some c20, some c808, some c338, some c160, some c158, some c70, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c187, c180, c379, c5, c835, c191, c190, c186, c836, c109, c20, c808, c338, c160, c158, c70] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c835 := derived835 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c836 := derived836 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c808 := derived808 a h
  have h12 : Entails.eval a c338 := h 337 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c180, some c191, some c190, some c13, some c186, some c808, some c338, some c160, some c158, some c70, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c5, c180, c191, c190, c13, c186, c808, c338, c160, c158, c70] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c808 := derived808 a h
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c187, some c180, some c828, some c379, some c5, some c837, some c838, some c9, some c105, some c13, some c27, some c85, some c251, some c128, some c371, some c35, some c364, some c106, some c373, some c92, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c787, c187, c180, c828, c379, c5, c837, c838, c9, c105, c13, c27, c85, c251, c128, c371, c35, c364, c106, c373, c92] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c837 := derived837 a h
  have h7 : Entails.eval a c838 := derived838 a h
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c35 := h 34 (by decide)
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c106 := h 105 (by decide)
  have h19 : Entails.eval a c373 := h 372 (by decide)
  have h20 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c828, some c379, some c5, some c839, some c111, some c112, some c761, some c76, some c822, some c371, some c85, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c787, c180, c828, c379, c5, c839, c111, c112, c761, c76, c822, c371, c85] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c839 := derived839 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c761 := derived761 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c822 := derived822 a h
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c838, some c13, some c9, some c105, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c5, c838, c13, c9, c105] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c838 := derived838 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨41, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨51, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c5, some c180, some c105, some c808, some c21, some c73, some c336, some c338, some c243, some c242, some c202, some c222, some c299, some c245, some c703, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c787, c5, c180, c105, c808, c21, c73, c336, c338, c243, c242, c202, c222, c299, c245, c703] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c808 := derived808 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c338 := h 337 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c242 := h 241 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c703 := derived703 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c101, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c109, c110, c101] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c828, some c379, some c187, some c840, some c375, some c819, some c366, some c821, some c370, some c841, some c842, some c843, some c20, some c190, some c175, some c834, some c26, some c76, some c4, some c247, some c125, some c371, some c754, some c36, some c229, some c257, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c787, c180, c828, c379, c187, c840, c375, c819, c366, c821, c370, c841, c842, c843, c20, c190, c175, c834, c26, c76, c4, c247, c125, c371, c754, c36, c229, c257] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c840 := derived840 a h
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c821 := derived821 a h
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c842 := derived842 a h
  have h13 : Entails.eval a c843 := derived843 a h
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c834 := derived834 a h
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c76 := h 75 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  have h21 : Entails.eval a c247 := h 246 (by decide)
  have h22 : Entails.eval a c125 := h 124 (by decide)
  have h23 : Entails.eval a c371 := h 370 (by decide)
  have h24 : Entails.eval a c754 := derived754 a h
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  have h27 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c828, some c379, some c844, some c378, some c589, some c186, some c190, some c179, some c799, some c800, some c841, some c204, some c256, some c127, some c27, some c40, some c375, some c109, some c365, some c76, some c173, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c787, c180, c828, c379, c844, c378, c589, c186, c190, c179, c799, c800, c841, c204, c256, c127, c27, c40, c375, c109, c365, c76, c173] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c589 := derived589 a h
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c799 := derived799 a h
  have h11 : Entails.eval a c800 := derived800 a h
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c40 := h 39 (by decide)
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c109 := h 108 (by decide)
  have h20 : Entails.eval a c365 := h 364 (by decide)
  have h21 : Entails.eval a c76 := h 75 (by decide)
  have h22 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨48, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c106, some c33, some c28, some c248, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c109, c106, c33, c28, c248] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c27, some c375, some c176, some c365, some c173, some c76, some c846, some c40, some c125, some c127, some c237, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c27, c375, c176, c365, c173, c76, c846, c40, c125, c127, c237] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c846 := derived846 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c726, some c173, some c237, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c78, c726, c173, c237] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c726 := derived726 a h
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c848, some c106, some c35, some c37, some c111, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c848, c106, c35, c37, c111] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c28, some c35, some c821, some c111, some c374, some c76, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c5, c28, c35, c821, c111, c374, c76] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c821 := derived821 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c844, some c589, some c186, some c378, some c180, some c828, some c379, some c5, some c190, some c179, some c1, some c845, some c847, some c251, some c256, some c849, some c125, some c850, some c106, some c78, some c34, some c173, some c111, some c76, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c787, c844, c589, c186, c378, c180, c828, c379, c5, c190, c179, c1, c845, c847, c251, c256, c849, c125, c850, c106, c78, c34, c173, c111, c76] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c844 := derived844 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c828 := derived828 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c845 := derived845 a h
  have h13 : Entails.eval a c847 := derived847 a h
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c256 := h 255 (by decide)
  have h16 : Entails.eval a c849 := derived849 a h
  have h17 : Entails.eval a c125 := h 124 (by decide)
  have h18 : Entails.eval a c850 := derived850 a h
  have h19 : Entails.eval a c106 := h 105 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c34 := h 33 (by decide)
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c111 := h 110 (by decide)
  have h24 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c4, some c173, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c76, c4, c173] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c826, some c833, some c200, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c826, c833, c200] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c826 := derived826 a h
  have h1 : Entails.eval a c833 := derived833 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c159, some c339, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c152, c159, c339] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c558, some c41, some c147, some c44, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c57, c558, c41, c147, c44] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c558 := derived558 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c852, some c111, some c34, some c35, some c855, some c563, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c78, c852, c111, c34, c35, c855, c563] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c852 := derived852 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c855 := derived855 a h
  have h6 : Entails.eval a c563 := derived563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c95, some c114, some c111, some c530, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c1, c95, c114, c111, c530] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c530 := derived530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c857, some c106, some c35, some c111, some c4, some c37, some c125, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c857, c106, c35, c111, c4, c37, c125] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c857 := derived857 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨14, by decide⟩, false), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c852, some c374, some c365, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c76, c852, c374, c365] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c852 := derived852 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c844, some c851, some c854, some c5, some c828, some c379, some c589, some c186, some c859, some c111, some c378, some c251, some c256, some c856, some c109, some c35, some c530, some c13, some c106, some c115, some c1, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c787, c180, c844, c851, c854, c5, c828, c379, c589, c186, c859, c111, c378, c251, c256, c856, c109, c35, c530, c13, c106, c115, c1] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c844 := derived844 a h
  have h3 : Entails.eval a c851 := derived851 a h
  have h4 : Entails.eval a c854 := derived854 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c828 := derived828 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c859 := derived859 a h
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c856 := derived856 a h
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c530 := derived530 a h
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c106 := h 105 (by decide)
  have h21 : Entails.eval a c115 := h 114 (by decide)
  have h22 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c1, some c162, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c73, c1, c162] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c854, some c68, some c157, some c132, some c339, some c52, some c130, some c147, some c300, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c854, c68, c157, c132, c339, c52, c130, c147, c300] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c854 := derived854 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c828, some c379, some c844, some c589, some c186, some c859, some c378, some c5, some c851, some c854, some c860, some c27, some c375, some c365, some c861, some c57, some c862, some c173, some c358, some c162, some c149, some c129, some c339, some c41, some c136, some c140, some c300, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c787, c180, c828, c379, c844, c589, c186, c859, c378, c5, c851, c854, c860, c27, c375, c365, c861, c57, c862, c173, c358, c162, c149, c129, c339, c41, c136, c140, c300] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c859 := derived859 a h
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c851 := derived851 a h
  have h11 : Entails.eval a c854 := derived854 a h
  have h12 : Entails.eval a c860 := derived860 a h
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c365 := h 364 (by decide)
  have h16 : Entails.eval a c861 := derived861 a h
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c862 := derived862 a h
  have h19 : Entails.eval a c173 := h 172 (by decide)
  have h20 : Entails.eval a c358 := h 357 (by decide)
  have h21 : Entails.eval a c162 := h 161 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c129 := h 128 (by decide)
  have h24 : Entails.eval a c339 := h 338 (by decide)
  have h25 : Entails.eval a c41 := h 40 (by decide)
  have h26 : Entails.eval a c136 := h 135 (by decide)
  have h27 : Entails.eval a c140 := h 139 (by decide)
  have h28 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c5, some c180, some c828, some c844, some c589, some c378, some c186, some c863, some c105, some c607, some c73, some c1, some c861, some c248, some c256, some c190, some c365, some c609, some c703, some c854, some c316, some c325, some c147, some c297, some c266, some c277, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c787, c5, c180, c828, c844, c589, c378, c186, c863, c105, c607, c73, c1, c861, c248, c256, c190, c365, c609, c703, c854, c316, c325, c147, c297, c266, c277] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c863 := derived863 a h
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c607 := derived607 a h
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c861 := derived861 a h
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c256 := h 255 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c609 := derived609 a h
  have h19 : Entails.eval a c703 := derived703 a h
  have h20 : Entails.eval a c854 := derived854 a h
  have h21 : Entails.eval a c316 := h 315 (by decide)
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c147 := h 146 (by decide)
  have h24 : Entails.eval a c297 := h 296 (by decide)
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c361, some c379, some c78, some c378, some c105, some c112, some c607, some c73, some c1, some c95, some c583, some c248, some c368, some c109, some c240, some c29, some c114, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c589, c361, c379, c78, c378, c105, c112, c607, c73, c1, c95, c583, c248, c368, c109, c240, c29, c114] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c607 := derived607 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c583 := derived583 a h
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  have h15 : Entails.eval a c240 := h 239 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨52, by decide⟩, true), (⟨46, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c361, some c78, some c378, some c251, some c256, some c234, some c858, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c589, c361, c78, c378, c251, c256, c234, c858] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c251 := h 250 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c858 := derived858 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨49, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c858, some c245, some c33, some c109, some c522, some c4, some c125, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c379, c858, c245, c33, c109, c522, c4, c125] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c858 := derived858 a h
  have h2 : Entails.eval a c245 := h 244 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨46, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c361, some c379, some c866, some c78, some c378, some c867, some c234, some c245, some c609, some c204, some c339, some c347, some c221, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c589, c361, c379, c866, c78, c378, c867, c234, c245, c609, c204, c339, c347, c221] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c866 := derived866 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c867 := derived867 a h
  have h7 : Entails.eval a c234 := h 233 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c609 := derived609 a h
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c347 := h 346 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c78, some c361, some c365, some c379, some c865, some c866, some c27, some c868, some c248, some c33, some c109, some c4, some c36, some c125, some c234, some c263, some c510, some c209, some c216, some c47, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c589, c78, c361, c365, c379, c865, c866, c27, c868, c248, c33, c109, c4, c36, c125, c234, c263, c510, c209, c216, c47] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c865 := derived865 a h
  have h6 : Entails.eval a c866 := derived866 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c868 := derived868 a h
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c510 := derived510 a h
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c852, some c111, some c23, some c245, some c33, some c109, some c826, some c833, some c853, some c40, some c132, some c125, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c379, c852, c111, c23, c245, c33, c109, c826, c833, c853, c40, c132, c125] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c852 := derived852 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c826 := derived826 a h
  have h8 : Entails.eval a c833 := derived833 a h
  have h9 : Entails.eval a c853 := derived853 a h
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c854, some c136, some c57, some c339, some c149, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c854, c136, c57, c339, c149] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c854 := derived854 a h
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, false), (⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c235, some c263, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c239, c235, c263] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c5, some c378, some c589, some c186, some c180, some c864, some c869, some c861, some c105, some c27, some c870, some c75, some c357, some c111, some c369, some c162, some c368, some c36, some c852, some c246, some c33, some c609, some c803, some c871, some c872, some c127, some c40, some c715, some c779, some c263, some c199, some c66, some c61, some c152, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c787, c5, c378, c589, c186, c180, c864, c869, c861, c105, c27, c870, c75, c357, c111, c369, c162, c368, c36, c852, c246, c33, c609, c803, c871, c872, c127, c40, c715, c779, c263, c199, c66, c61, c152] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c589 := derived589 a h
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c864 := derived864 a h
  have h7 : Entails.eval a c869 := derived869 a h
  have h8 : Entails.eval a c861 := derived861 a h
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c870 := derived870 a h
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c162 := h 161 (by decide)
  have h17 : Entails.eval a c368 := h 367 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c852 := derived852 a h
  have h20 : Entails.eval a c246 := h 245 (by decide)
  have h21 : Entails.eval a c33 := h 32 (by decide)
  have h22 : Entails.eval a c609 := derived609 a h
  have h23 : Entails.eval a c803 := derived803 a h
  have h24 : Entails.eval a c871 := derived871 a h
  have h25 : Entails.eval a c872 := derived872 a h
  have h26 : Entails.eval a c127 := h 126 (by decide)
  have h27 : Entails.eval a c40 := h 39 (by decide)
  have h28 : Entails.eval a c715 := derived715 a h
  have h29 : Entails.eval a c779 := derived779 a h
  have h30 : Entails.eval a c263 := h 262 (by decide)
  have h31 : Entails.eval a c199 := h 198 (by decide)
  have h32 : Entails.eval a c66 := h 65 (by decide)
  have h33 : Entails.eval a c61 := h 60 (by decide)
  have h34 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c787, some c5, some c180, some c589, some c378, some c186, some c869, some c861, some c873, some c256, some c583, some c111, some c852, some c379, some c357, some c369, some c162, some c579, some c28, some c235, some c129, some c60, some c569, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c864, c787, c5, c180, c589, c378, c186, c869, c861, c873, c256, c583, c111, c852, c379, c357, c369, c162, c579, c28, c235, c129, c60, c569] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c787 := derived787 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c869 := derived869 a h
  have h8 : Entails.eval a c861 := derived861 a h
  have h9 : Entails.eval a c873 := derived873 a h
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c583 := derived583 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c852 := derived852 a h
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c579 := derived579 a h
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c235 := h 234 (by decide)
  have h21 : Entails.eval a c129 := h 128 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c569 := derived569 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c190, some c5, some c180, some c175, some c362, some c379, some c852, some c364, some c111, some c834, some c372, some c23, some c22, some c245, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c187, c190, c5, c180, c175, c362, c379, c852, c364, c111, c834, c372, c23, c22, c245] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c852 := derived852 a h
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c834 := derived834 a h
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c874, some c864, some c787, some c5, some c180, some c111, some c75, some c583, some c245, some c834, some c33, some c9, some c105, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c874, c864, c787, c5, c180, c111, c75, c583, c245, c834, c33, c9, c105] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c874 := derived874 a h
  have h1 : Entails.eval a c864 := derived864 a h
  have h2 : Entails.eval a c787 := derived787 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c583 := derived583 a h
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c834 := derived834 a h
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨9, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c106, some c9, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c843, c106, c9] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨46, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c251, some c4, some c101, some c877, some c26, some c86, some c125, some c112, some c36, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c379, c251, c4, c101, c877, c26, c86, c125, c112, c36] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c877 := derived877 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c864, some c874, some c875, some c187, some c190, some c5, some c180, some c876, some c878, some c75, some c361, some c362, some c112, some c380, some c76, some c4, some c101, some c877, some c26, some c807, some c92, some c247, some c125, some c370, some c176, some c36, some c357, some c841, some c812, some c243, some c802, some c225, some c229, some c321, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c787, c864, c874, c875, c187, c190, c5, c180, c876, c878, c75, c361, c362, c112, c380, c76, c4, c101, c877, c26, c807, c92, c247, c125, c370, c176, c36, c357, c841, c812, c243, c802, c225, c229, c321] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c864 := derived864 a h
  have h2 : Entails.eval a c874 := derived874 a h
  have h3 : Entails.eval a c875 := derived875 a h
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c876 := derived876 a h
  have h9 : Entails.eval a c878 := derived878 a h
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c877 := derived877 a h
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c807 := derived807 a h
  have h21 : Entails.eval a c92 := h 91 (by decide)
  have h22 : Entails.eval a c247 := h 246 (by decide)
  have h23 : Entails.eval a c125 := h 124 (by decide)
  have h24 : Entails.eval a c370 := h 369 (by decide)
  have h25 : Entails.eval a c176 := h 175 (by decide)
  have h26 : Entails.eval a c36 := h 35 (by decide)
  have h27 : Entails.eval a c357 := h 356 (by decide)
  have h28 : Entails.eval a c841 := derived841 a h
  have h29 : Entails.eval a c812 := derived812 a h
  have h30 : Entails.eval a c243 := h 242 (by decide)
  have h31 : Entails.eval a c802 := derived802 a h
  have h32 : Entails.eval a c225 := h 224 (by decide)
  have h33 : Entails.eval a c229 := h 228 (by decide)
  have h34 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨46, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c234, some c361, some c380, some c4, some c101, some c125, some c877, some c36, some c92, some c370, some c357, some c230, some c243, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c234, c361, c380, c4, c101, c125, c877, c36, c92, c370, c357, c230, c243] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c234 := h 233 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c877 := derived877 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c874, some c187, some c864, some c5, some c180, some c190, some c875, some c879, some c23, some c234, some c111, some c112, some c127, some c235, some c880, some c379, some c4, some c101, some c125, some c877, some c36, some c92, some c370, some c176, some c230, some c841, some c812, some c257, some c223, some c227, some c66, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c787, c874, c187, c864, c5, c180, c190, c875, c879, c23, c234, c111, c112, c127, c235, c880, c379, c4, c101, c125, c877, c36, c92, c370, c176, c230, c841, c812, c257, c223, c227, c66] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c874 := derived874 a h
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c864 := derived864 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c875 := derived875 a h
  have h8 : Entails.eval a c879 := derived879 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c234 := h 233 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c127 := h 126 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c880 := derived880 a h
  have h16 : Entails.eval a c379 := h 378 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c101 := h 100 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c877 := derived877 a h
  have h21 : Entails.eval a c36 := h 35 (by decide)
  have h22 : Entails.eval a c92 := h 91 (by decide)
  have h23 : Entails.eval a c370 := h 369 (by decide)
  have h24 : Entails.eval a c176 := h 175 (by decide)
  have h25 : Entails.eval a c230 := h 229 (by decide)
  have h26 : Entails.eval a c841 := derived841 a h
  have h27 : Entails.eval a c812 := derived812 a h
  have h28 : Entails.eval a c257 := h 256 (by decide)
  have h29 : Entails.eval a c223 := h 222 (by decide)
  have h30 : Entails.eval a c227 := h 226 (by decide)
  have h31 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c829, some c134, some c338, some c152, some c149, some c333, some c57, some c1, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c829, c134, c338, c152, c149, c333, c57, c1] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c829 := derived829 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c338 := h 337 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c787, some c180, some c5, some c864, some c874, some c187, some c881, some c186, some c380, some c882, some c838, some c191, some c843, some c20, some c112, some c808, some c75, some c583, some c23, some c338, some c245, some c703, some c134, some c299, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c787, c180, c5, c864, c874, c187, c881, c186, c380, c882, c838, c191, c843, c20, c112, c808, c75, c583, c23, c338, c245, c703, c134, c299] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c787 := derived787 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c864 := derived864 a h
  have h4 : Entails.eval a c874 := derived874 a h
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c881 := derived881 a h
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c882 := derived882 a h
  have h10 : Entails.eval a c838 := derived838 a h
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c843 := derived843 a h
  have h13 : Entails.eval a c20 := h 19 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c808 := derived808 a h
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c583 := derived583 a h
  have h18 : Entails.eval a c23 := h 22 (by decide)
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c245 := h 244 (by decide)
  have h21 : Entails.eval a c703 := derived703 a h
  have h22 : Entails.eval a c134 := h 133 (by decide)
  have h23 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived883

end CochromaticTwenty.Certificates.B16_2_2
