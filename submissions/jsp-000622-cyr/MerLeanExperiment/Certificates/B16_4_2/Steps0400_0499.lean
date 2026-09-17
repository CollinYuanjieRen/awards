import MerLeanExperiment.Certificates.B16_4_2.Steps0300_0399

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c784 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c332, some c359, some c783, some c353, some c321, some c76, some c239, some c266, some c210, some c265, some c33, some c132, some c110, some c106, some c215, some c53, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c20, c332, c359, c783, c353, c321, c76, c239, c266, c210, c265, c33, c132, c110, c106, c215, c53] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c353 := h 352 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c215 := h 214 (by decide)
  have h16 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨45, by decide⟩, false), (⟨38, by decide⟩, true), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c784, some c32, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c784, c32] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c784 := derived784 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨38, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c118, some c780, some c207, some c204, some c9, some c170, some c775, some c20, some c359, some c332, some c781, some c11, some c785, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c146, c118, c780, c207, c204, c9, c170, c775, c20, c359, c332, c781, c11, c785] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c780 := derived780 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c775 := derived775 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c781 := derived781 a h
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c785 := derived785 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨35, by decide⟩, true), (⟨18, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c631, some c226, some c706, some c743, some c25, some c353, some c231, some c513, some c704, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c18, c631, c226, c706, c743, c25, c353, c231, c513, c704] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c226 := h 225 (by decide)
  have h3 : Entails.eval a c706 := derived706 a h
  have h4 : Entails.eval a c743 := derived743 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c513 := derived513 a h
  have h9 : Entails.eval a c704 := derived704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨35, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c269, some c5, some c11, some c112, some c28, some c271, some c787, some c266, some c265, some c231, some c703, some c127, some c336, some c87, some c243, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c269, c5, c11, c112, c28, c271, c787, c266, c265, c231, c703, c127, c336, c87, c243] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c787 := derived787 a h
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c703 := derived703 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c107, some c35, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c105, c107, c35] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c788, some c39, some c19, some c602, some c271, some c734, some c144, some c125, some c266, some c332, some c139, some c789, some c66, some c353, some c532, some c175, some c203, some c147, some c119, some c219, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c204, c788, c39, c19, c602, c271, c734, c144, c125, c266, c332, c139, c789, c66, c353, c532, c175, c203, c147, c119, c219] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c788 := derived788 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c602 := derived602 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c734 := derived734 a h
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c789 := derived789 a h
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c532 := derived532 a h
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c147 := h 146 (by decide)
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c638, some c117, some c139, some c204, some c360, some c359, some c206, some c168, some c144, some c16, some c221, some c24, some c146, some c354, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c271, c638, c117, c139, c204, c360, c359, c206, c168, c144, c16, c221, c24, c146, c354] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c359, some c168, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c360, c359, c168] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨33, by decide⟩, false), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c269, some c791, some c208, some c207, some c792, some c235, some c228, some c355, some c356, some c168, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c271, c269, c791, c208, c207, c792, c235, c228, c355, c356, c168] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c791 := derived791 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨36, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c219, some c21, some c12, some c105, some c112, some c40, some c54, some c221, some c211, some c315, some c154, some c631, some c155, some c202, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c271, c219, c21, c12, c105, c112, c40, c54, c221, c211, c315, c154, c631, c155, c202] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c221 := h 220 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c631 := derived631 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨43, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c269, some c21, some c228, some c12, some c105, some c112, some c325, some c40, some c26, some c122, some c221, some c266, some c205, some c146, some c235, some c358, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c269, c21, c228, c12, c105, c112, c325, c40, c26, c122, c221, c266, c205, c146, c235, c358] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨36, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c794, some c123, some c795, some c265, some c222, some c631, some c41, some c1, some c112, some c26, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c794, c123, c795, c265, c222, c631, c41, c1, c112, c26] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c794 := derived794 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c795 := derived795 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c21, some c222, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c41, c21, c222] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c147, some c797, some c12, some c207, some c272, some c265, some c222, some c115, some c631, some c1, some c17, some c26, some c112, some c72, some c356, some c69, some c165, some c205, some c172, some c354, some c685, some c283, some c8, some c224, some c24, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c119, c147, c797, c12, c207, c272, c265, c222, c115, c631, c1, c17, c26, c112, c72, c356, c69, c165, c205, c172, c354, c685, c283, c8, c224, c24] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c631 := derived631 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c356 := h 355 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c172 := h 171 (by decide)
  have h20 : Entails.eval a c354 := h 353 (by decide)
  have h21 : Entails.eval a c685 := derived685 a h
  have h22 : Entails.eval a c283 := h 282 (by decide)
  have h23 : Entails.eval a c8 := h 7 (by decide)
  have h24 : Entails.eval a c224 := h 223 (by decide)
  have h25 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c356, some c228, some c69, some c165, some c205, some c134, some c269, some c270, some c33, some c135, some c8, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c115, c356, c228, c69, c165, c205, c134, c269, c270, c33, c135, c8] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨36, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c119, some c799, some c219, some c143, some c356, some c69, some c165, some c276, some c205, some c154, some c317, some c318, some c155, some c61, some c8, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c147, c119, c799, c219, c143, c356, c69, c165, c276, c205, c154, c317, c318, c155, c61, c8] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c799 := derived799 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c797, some c112, some c105, some c219, some c143, some c54, some c356, some c211, some c228, some c27, some c268, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c797, c112, c105, c219, c143, c54, c356, c211, c228, c27, c268] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c797 := derived797 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c211 := h 210 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c147, some c797, some c105, some c112, some c801, some c115, some c26, some c356, some c267, some c211, some c165, some c235, some c37, some c205, some c354, some c172, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c119, c147, c797, c105, c112, c801, c115, c26, c356, c267, c211, c165, c235, c37, c205, c354, c172] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c801 := derived801 a h
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c798, some c119, some c147, some c797, some c12, some c207, some c802, some c799, some c800, some c219, some c313, some c143, some c150, some c356, some c1, some c228, some c165, some c37, some c268, some c205, some c27, some c172, some c267, some c354, some c235, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c798, c119, c147, c797, c12, c207, c802, c799, c800, c219, c313, c143, c150, c356, c1, c228, c165, c37, c268, c205, c27, c172, c267, c354, c235] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c798 := derived798 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c802 := derived802 a h
  have h7 : Entails.eval a c799 := derived799 a h
  have h8 : Entails.eval a c800 := derived800 a h
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c228 := h 227 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c27 := h 26 (by decide)
  have h21 : Entails.eval a c172 := h 171 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  have h23 : Entails.eval a c354 := h 353 (by decide)
  have h24 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c147, some c797, some c207, some c12, some c798, some c803, some c20, some c40, some c72, some c105, some c112, some c67, some c602, some c796, some c234, some c354, some c235, some c267, some c224, some c26, some c283, some c219, some c313, some c54, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c119, c147, c797, c207, c12, c798, c803, c20, c40, c72, c105, c112, c67, c602, c796, c234, c354, c235, c267, c224, c26, c283, c219, c313, c54] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c798 := derived798 a h
  have h6 : Entails.eval a c803 := derived803 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c602 := derived602 a h
  have h14 : Entails.eval a c796 := derived796 a h
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c267 := h 266 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c283 := h 282 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c313 := h 312 (by decide)
  have h24 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨36, by decide⟩, false), (⟨12, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c797, some c105, some c112, some c801, some c115, some c123, some c26, some c329, some c211, some c180, some c54, some c295, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c797, c105, c112, c801, c115, c123, c26, c329, c211, c180, c54, c295] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c797 := derived797 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c801 := derived801 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c168, some c147, some c115, some c123, some c356, some c329, some c228, some c165, some c124, some c180, some c269, some c295, some c134, some c206, some c135, some c517, some c155, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c168, c147, c115, c123, c356, c329, c228, c165, c124, c180, c269, c295, c134, c206, c135, c517, c155] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c168 := h 167 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c517 := derived517 a h
  have h16 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c27, some c1, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c631, c27, c1] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c804, some c168, some c119, some c147, some c797, some c805, some c806, some c219, some c143, some c356, some c228, some c69, some c165, some c268, some c807, some c267, some c137, some c33, some c8, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c804, c168, c119, c147, c797, c805, c806, c219, c143, c356, c228, c69, c165, c268, c807, c267, c137, c33, c8] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c804 := derived804 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c797 := derived797 a h
  have h5 : Entails.eval a c805 := derived805 a h
  have h6 : Entails.eval a c806 := derived806 a h
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c807 := derived807 a h
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  have h17 : Entails.eval a c33 := h 32 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c47, some c54, some c345, some c259, some c105, some c100, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c39, c47, c54, c345, c259, c105, c100] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c219, some c211, some c235, some c809, some c10, some c150, some c201, some c1, some c808, some c37, some c355, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c272, c219, c211, c235, c809, c10, c150, c201, c1, c808, c37, c355] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c809 := derived809 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c808 := derived808 a h
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨45, by decide⟩, true), (⟨11, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c47, some c54, some c331, some c359, some c345, some c313, some c315, some c287, some c95, some c283, some c155, some c174, some c185, some c188, some c336, some c369, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c39, c47, c54, c331, c359, c345, c313, c315, c287, c95, c283, c155, c174, c185, c188, c336, c369] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨32, by decide⟩, true), (⟨43, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c355, some c336, some c66, some c179, some c356, some c276, some c65, some c213, some c316, some c114, some c61, some c8, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c283, c355, c336, c66, c179, c356, c276, c65, c213, c316, c114, c61, c8] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c353, some c66, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c360, c353, c66] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c32, some c105, some c112, some c14, some c119, some c136, some c127, some c207, some c90, some c811, some c320, some c295, some c813, some c812, some c315, some c300, some c37, some c55, some c179, some c323, some c316, some c174, some c276, some c202, some c582, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c20, c32, c105, c112, c14, c119, c136, c127, c207, c90, c811, c320, c295, c813, c812, c315, c300, c37, c55, c179, c323, c316, c174, c276, c202, c582] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c811 := derived811 a h
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c813 := derived813 a h
  have h14 : Entails.eval a c812 := derived812 a h
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c300 := h 299 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c55 := h 54 (by decide)
  have h19 : Entails.eval a c179 := h 178 (by decide)
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c316 := h 315 (by decide)
  have h22 : Entails.eval a c174 := h 173 (by decide)
  have h23 : Entails.eval a c276 := h 275 (by decide)
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c582 := derived582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c807, some c814, some c219, some c211, some c267, some c809, some c810, some c10, some c359, some c143, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c20, c807, c814, c219, c211, c267, c809, c810, c10, c359, c143] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c814 := derived814 a h
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c809 := derived809 a h
  have h7 : Entails.eval a c810 := derived810 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c150, some c1, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c54, c150, c1] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨37, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c313, some c315, some c631, some c155, some c59, some c283, some c201, some c202, some c432, some c354, some c355, some c172, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c211, c313, c315, c631, c155, c59, c283, c201, c202, c432, c354, c355, c172] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c432 := derived432 a h
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨52, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c47, some c272, some c259, some c228, some c117, some c268, some c253, some c12, some c124, some c88, some c816, some c817, some c51, some c305, some c308, some c105, some c14, some c317, some c147, some c58, some c109, some c89, some c65, some c246, some c355, some c270, some c235, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c111, c47, c272, c259, c228, c117, c268, c253, c12, c124, c88, c816, c817, c51, c305, c308, c105, c14, c317, c147, c58, c109, c89, c65, c246, c355, c270, c235] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c816 := derived816 a h
  have h12 : Entails.eval a c817 := derived817 a h
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  have h22 : Entails.eval a c89 := h 88 (by decide)
  have h23 : Entails.eval a c65 := h 64 (by decide)
  have h24 : Entails.eval a c246 := h 245 (by decide)
  have h25 : Entails.eval a c355 := h 354 (by decide)
  have h26 : Entails.eval a c270 := h 269 (by decide)
  have h27 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false), (⟨37, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c816, some c817, some c12, some c47, some c39, some c356, some c345, some c228, some c818, some c123, some c329, some c124, some c269, some c30, some c109, some c38, some c214, some c156, some c308, some c14, some c347, some c43, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c111, c816, c817, c12, c47, c39, c356, c345, c228, c818, c123, c329, c124, c269, c30, c109, c38, c214, c156, c308, c14, c347, c43] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c816 := derived816 a h
  have h2 : Entails.eval a c817 := derived817 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c818 := derived818 a h
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c329 := h 328 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c156 := h 155 (by decide)
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c347 := h 346 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨31, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c43, some c14, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c147, c43, c14] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, true), (⟨39, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨12, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c39, some c47, some c347, some c123, some c26, some c331, some c267, some c180, some c135, some c31, some c88, some c374, some c240, some c365, some c177, some c214, some c341, some c8, some c38, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c111, c39, c47, c347, c123, c26, c331, c267, c180, c135, c31, c88, c374, c240, c365, c177, c214, c341, c8, c38] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c374 := h 373 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, false), (⟨37, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c816, some c12, some c47, some c39, some c817, some c819, some c144, some c116, some c820, some c347, some c51, some c105, some c14, some c821, some c257, some c268, some c818, some c341, some c305, some c317, some c160, some c58, some c312, some c109, some c25, some c93, some c267, some c186, some c235, some c163, some c355, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c111, c816, c12, c47, c39, c817, c819, c144, c116, c820, c347, c51, c105, c14, c821, c257, c268, c818, c341, c305, c317, c160, c58, c312, c109, c25, c93, c267, c186, c235, c163, c355] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c816 := derived816 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c817 := derived817 a h
  have h6 : Entails.eval a c819 := derived819 a h
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c820 := derived820 a h
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c821 := derived821 a h
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c818 := derived818 a h
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c305 := h 304 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c160 := h 159 (by decide)
  have h22 : Entails.eval a c58 := h 57 (by decide)
  have h23 : Entails.eval a c312 := h 311 (by decide)
  have h24 : Entails.eval a c109 := h 108 (by decide)
  have h25 : Entails.eval a c25 := h 24 (by decide)
  have h26 : Entails.eval a c93 := h 92 (by decide)
  have h27 : Entails.eval a c267 := h 266 (by decide)
  have h28 : Entails.eval a c186 := h 185 (by decide)
  have h29 : Entails.eval a c235 := h 234 (by decide)
  have h30 : Entails.eval a c163 := h 162 (by decide)
  have h31 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨45, by decide⟩, true), (⟨15, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c143, some c136, some c156, some c271, some c268, some c228, some c133, some c240, some c341, some c305, some c317, some c160, some c206, some c155, some c648, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c143, c136, c156, c271, c268, c228, c133, c240, c341, c305, c317, c160, c206, c155, c648] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c240 := h 239 (by decide)
  have h8 : Entails.eval a c341 := h 340 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c648 := derived648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, true), (⟨37, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c143, some c257, some c268, some c48, some c228, some c133, some c341, some c205, some c305, some c154, some c317, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c143, c257, c268, c48, c228, c133, c341, c205, c305, c154, c317] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, true), (⟨39, by decide⟩, false), (⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c143, some c127, some c331, some c123, some c347, some c360, some c824, some c20, some c356, some c345, some c228, some c48, some c95, some c253, some c305, some c317, some c160, some c312, some c205, some c186, some c161, some c174, some c323, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c143, c127, c331, c123, c347, c360, c824, c20, c356, c345, c228, c48, c95, c253, c305, c317, c160, c312, c205, c186, c161, c174, c323] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c331 := h 330 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c824 := derived824 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c95 := h 94 (by decide)
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c186 := h 185 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c174 := h 173 (by decide)
  have h22 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c143, some c820, some c360, some c347, some c51, some c105, some c14, some c127, some c90, some c331, some c123, some c823, some c12, some c825, some c521, some c271, some c209, some c20, some c356, some c345, some c276, some c48, some c95, some c317, some c160, some c312, some c282, some c205, some c186, some c338, some c161, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c143, c820, c360, c347, c51, c105, c14, c127, c90, c331, c123, c823, c12, c825, c521, c271, c209, c20, c356, c345, c276, c48, c95, c317, c160, c312, c282, c205, c186, c338, c161] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c820 := derived820 a h
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c331 := h 330 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c823 := derived823 a h
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c825 := derived825 a h
  have h14 : Entails.eval a c521 := derived521 a h
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c20 := h 19 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c276 := h 275 (by decide)
  have h21 : Entails.eval a c48 := h 47 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  have h23 : Entails.eval a c317 := h 316 (by decide)
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c312 := h 311 (by decide)
  have h26 : Entails.eval a c282 := h 281 (by decide)
  have h27 : Entails.eval a c205 := h 204 (by decide)
  have h28 : Entails.eval a c186 := h 185 (by decide)
  have h29 : Entails.eval a c338 := h 337 (by decide)
  have h30 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨17, by decide⟩, false), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c155, some c143, some c127, some c331, some c287, some c174, some c202, some c154, some c140, some c210, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c315, c155, c143, c127, c331, c287, c174, c202, c154, c140, c210] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c36, some c16, some c119, some c827, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c211, c36, c16, c119, c827] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c827 := derived827 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨31, by decide⟩, true), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c202, some c206, some c36, some c16, some c119, some c127, some c133, some c153, some c347, some c331, some c268, some c317, some c174, some c136, some c308, some c371, some c286, some c197, some c382, some c368, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c15, c202, c206, c36, c16, c119, c127, c133, c153, c347, c331, c268, c317, c174, c136, c308, c371, c286, c197, c382, c368] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c347 := h 346 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c174 := h 173 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c286 := h 285 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c382 := h 381 (by decide)
  have h20 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c47, some c143, some c314, some c210, some c155, some c59, some c206, some c15, some c30, some c828, some c829, some c265, some c267, some c259, some c34, some c51, some c105, some c16, some c147, some c153, some c360, some c317, some c117, some c235, some c156, some c308, some c12, some c355, some c345, some c67, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c47, c143, c314, c210, c155, c59, c206, c15, c30, c828, c829, c265, c267, c259, c34, c51, c105, c16, c147, c153, c360, c317, c117, c235, c156, c308, c12, c355, c345, c67] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c155 := h 154 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c828 := derived828 a h
  have h10 : Entails.eval a c829 := derived829 a h
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c147 := h 146 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c117 := h 116 (by decide)
  have h23 : Entails.eval a c235 := h 234 (by decide)
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c308 := h 307 (by decide)
  have h26 : Entails.eval a c12 := h 11 (by decide)
  have h27 : Entails.eval a c355 := h 354 (by decide)
  have h28 : Entails.eval a c345 := h 344 (by decide)
  have h29 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c442, some c265, some c267, some c34, some c139, some c816, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c54, c442, c265, c267, c34, c139, c816] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c816 := derived816 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c150, some c202, some c54, some c2, some c831, some c266, some c135, some c107, some c47, some c143, some c265, some c259, some c139, some c104, some c816, some c201, some c186, some c21, some c301, some c360, some c341, some c191, some c165, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c150, c202, c54, c2, c831, c266, c135, c107, c47, c143, c265, c259, c139, c104, c816, c201, c186, c21, c301, c360, c341, c191, c165] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c150 := h 149 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c831 := derived831 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c816 := derived816 a h
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c186 := h 185 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c341 := h 340 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c150, some c2, some c202, some c47, some c143, some c107, some c831, some c266, some c120, some c832, some c465, some c347, some c355, some c104, some c273, some c186, some c341, some c301, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c54, c150, c2, c202, c47, c143, c107, c831, c266, c120, c832, c465, c347, c355, c104, c273, c186, c341, c301] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c143 := h 142 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c831 := derived831 a h
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c832 := derived832 a h
  have h11 : Entails.eval a c465 := derived465 a h
  have h12 : Entails.eval a c347 := h 346 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c186 := h 185 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c202, some c360, some c347, some c469, some c355, some c273, some c341, some c358, some c301, some c74, some c186, some c105, some c104, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c2, c202, c360, c347, c469, c355, c273, c341, c358, c301, c74, c186, c105, c104] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c469 := derived469 a h
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c47, some c143, some c830, some c54, some c150, some c202, some c155, some c318, some c833, some c834, some c465, some c265, some c267, some c460, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c47, c143, c830, c54, c150, c202, c155, c318, c833, c834, c465, c265, c267, c460] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c830 := derived830 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c833 := derived833 a h
  have h9 : Entails.eval a c834 := derived834 a h
  have h10 : Entails.eval a c465 := derived465 a h
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c460 := derived460 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c834, some c465, some c462, some c224, some c135, some c460, some c272, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c202, c834, c465, c462, c224, c135, c460, c272] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c462 := derived462 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c460 := derived460 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c462, some c76, some c685, some c354, some c358, some c273, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c462, c76, c685, c354, c358, c273] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c462 := derived462 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c685 := derived685 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c155, some c47, some c143, some c837, some c360, some c347, some c51, some c224, some c797, some c135, some c816, some c272, some c117, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c54, c155, c47, c143, c837, c360, c347, c51, c224, c797, c135, c816, c272, c117] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  have h4 : Entails.eval a c837 := derived837 a h
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c347 := h 346 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c797 := derived797 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c816 := derived816 a h
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c47, some c143, some c835, some c631, some c202, some c155, some c314, some c318, some c54, some c2, some c836, some c107, some c838, some c442, some c465, some c223, some c347, some c120, some c104, some c355, some c186, some c273, some c301, some c341, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c47, c143, c835, c631, c202, c155, c314, c318, c54, c2, c836, c107, c838, c442, c465, c223, c347, c120, c104, c355, c186, c273, c301, c341] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c835 := derived835 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c836 := derived836 a h
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c838 := derived838 a h
  have h13 : Entails.eval a c442 := derived442 a h
  have h14 : Entails.eval a c465 := derived465 a h
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c347 := h 346 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c104 := h 103 (by decide)
  have h19 : Entails.eval a c355 := h 354 (by decide)
  have h20 : Entails.eval a c186 := h 185 (by decide)
  have h21 : Entails.eval a c273 := h 272 (by decide)
  have h22 : Entails.eval a c301 := h 300 (by decide)
  have h23 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c155, some c318, some c54, some c47, some c143, some c107, some c106, some c838, some c442, some c465, some c223, some c347, some c120, some c128, some c355, some c336, some c273, some c341, some c328, some c365, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c155, c318, c54, c47, c143, c107, c106, c838, c442, c465, c223, c347, c120, c128, c355, c336, c273, c341, c328, c365] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c155 := h 154 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c838 := derived838 a h
  have h8 : Entails.eval a c442 := derived442 a h
  have h9 : Entails.eval a c465 := derived465 a h
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c347 := h 346 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c273 := h 272 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c328 := h 327 (by decide)
  have h19 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c347, some c51, some c797, some c1, some c117, some c145, some c222, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c360, c347, c51, c797, c1, c117, c145, c222] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c224, some c462, some c360, some c841, some c75, some c105, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c24, c224, c462, c360, c841, c75, c105] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c224 := h 223 (by decide)
  have h2 : Entails.eval a c462 := derived462 a h
  have h3 : Entails.eval a c360 := h 359 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, true), (⟨40, by decide⟩, false), (⟨25, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c355, some c170, some c273, some c358, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c360, c355, c170, c273, c358] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨26, by decide⟩, true), (⟨40, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c358, some c273, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c354, c358, c273] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c753, some c172, some c76, some c424, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c109, c753, c172, c76, c424] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c424 := derived424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c465, some c172, some c265, some c201, some c203, some c139, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c465, c172, c265, c201, c203, c139] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c465 := derived465 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨33, by decide⟩, true), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨14, by decide⟩, true), (⟨30, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c273, some c141, some c37, some c844, some c118, some c223, some c274, some c356, some c275, some c221, some c227, some c20, some c845, some c46, some c341, some c344, some c47, some c302, some c111, some c846, some c360, some c843, some c74, some c185, some c106, some c103, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c318, c273, c141, c37, c844, c118, c223, c274, c356, c275, c221, c227, c20, c845, c46, c341, c344, c47, c302, c111, c846, c360, c843, c74, c185, c106, c103] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c845 := derived845 a h
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c302 := h 301 (by decide)
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c846 := derived846 a h
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c843 := derived843 a h
  have h23 : Entails.eval a c74 := h 73 (by decide)
  have h24 : Entails.eval a c185 := h 184 (by decide)
  have h25 : Entails.eval a c106 := h 105 (by decide)
  have h26 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c111, some c170, some c765, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c1, c111, c170, c765] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c765 := derived765 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨14, by decide⟩, true), (⟨30, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c141, some c37, some c275, some c20, some c845, some c46, some c344, some c848, some c56, some c319, some c274, some c847, some c341, some c307, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c273, c141, c37, c275, c20, c845, c46, c344, c848, c56, c319, c274, c847, c341, c307] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c845 := derived845 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c848 := derived848 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c847 := derived847 a h
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c141, some c37, some c845, some c848, some c765, some c56, some c21, some c218, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c273, c141, c37, c845, c848, c765, c56, c21, c218] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c848 := derived848 a h
  have h5 : Entails.eval a c765 := derived765 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨14, by decide⟩, true), (⟨30, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c118, some c37, some c849, some c356, some c582, some c274, some c786, some c19, some c70, some c106, some c850, some c33, some c223, some c266, some c61, some c782, some c807, some c319, some c63, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c273, c118, c37, c849, c356, c582, c274, c786, c19, c70, c106, c850, c33, c223, c266, c61, c782, c807, c319, c63] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c582 := derived582 a h
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c786 := derived786 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c850 := derived850 a h
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c782 := derived782 a h
  have h17 : Entails.eval a c807 := derived807 a h
  have h18 : Entails.eval a c319 := h 318 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨39, by decide⟩, true), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨22, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c33, some c356, some c582, some c266, some c782, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c72, c33, c356, c582, c266, c782] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c582 := derived582 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c782 := derived782 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c118, some c146, some c141, some c37, some c465, some c462, some c172, some c201, some c203, some c424, some c837, some c685, some c106, some c852, some c845, some c46, some c344, some c52, some c847, some c223, some c219, some c135, some c31, some c786, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c273, c118, c146, c141, c37, c465, c462, c172, c201, c203, c424, c837, c685, c106, c852, c845, c46, c344, c52, c847, c223, c219, c135, c31, c786] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c465 := derived465 a h
  have h6 : Entails.eval a c462 := derived462 a h
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c424 := derived424 a h
  have h11 : Entails.eval a c837 := derived837 a h
  have h12 : Entails.eval a c685 := derived685 a h
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c852 := derived852 a h
  have h15 : Entails.eval a c845 := derived845 a h
  have h16 : Entails.eval a c46 := h 45 (by decide)
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c847 := derived847 a h
  have h20 : Entails.eval a c223 := h 222 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  have h22 : Entails.eval a c135 := h 134 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c786 := derived786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c513, some c223, some c24, some c120, some c4, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c513, c223, c24, c120, c4] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c513 := derived513 a h
  have h1 : Entails.eval a c223 := h 222 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c141, some c146, some c118, some c854, some c853, some c851, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c37, c141, c146, c118, c854, c853, c851] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c854 := derived854 a h
  have h5 : Entails.eval a c853 := derived853 a h
  have h6 : Entails.eval a c851 := derived851 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨39, by decide⟩, false), (⟨11, by decide⟩, false), (⟨35, by decide⟩, true), (⟨18, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c4, some c70, some c128, some c80, some c336, some c328, some c241, some c237, some c122, some c265, some c5, some c139, some c28, some c1, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c106, c4, c70, c128, c80, c336, c328, c241, c237, c122, c265, c5, c139, c28, c1] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨39, by decide⟩, false), (⟨35, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c128, some c460, some c336, some c328, some c271, some c241, some c226, some c265, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c128, c460, c336, c328, c271, c241, c226, c265] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c128 := h 127 (by decide)
  have h1 : Entails.eval a c460 := derived460 a h
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨39, by decide⟩, false), (⟨11, by decide⟩, false), (⟨36, by decide⟩, false), (⟨18, by decide⟩, true), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c1, some c170, some c132, some c125, some c204, some c334, some c332, some c180, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c35, c1, c170, c132, c125, c204, c334, c332, c180] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨39, by decide⟩, false), (⟨27, by decide⟩, false), (⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c582, some c356, some c146, some c118, some c221, some c269, some c854, some c856, some c857, some c203, some c858, some c271, some c226, some c265, some c127, some c133, some c336, some c204, some c243, some c156, some c295, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c582, c356, c146, c118, c221, c269, c854, c856, c857, c203, c858, c271, c226, c265, c127, c133, c336, c204, c243, c156, c295] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c582 := derived582 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c854 := derived854 a h
  have h7 : Entails.eval a c856 := derived856 a h
  have h8 : Entails.eval a c857 := derived857 a h
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c858 := derived858 a h
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c336 := h 335 (by decide)
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c243 := h 242 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨35, by decide⟩, true), (⟨28, by decide⟩, true), (⟨22, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c223, some c266, some c782, some c1, some c201, some c207, some c156, some c157, some c320, some c4, some c63, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c223, c266, c782, c1, c201, c207, c156, c157, c320, c4, c63] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c223 := h 222 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c782 := derived782 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c146, some c141, some c37, some c273, some c855, some c221, some c275, some c356, some c582, some c274, some c860, some c859, some c465, some c462, some c846, some c219, some c226, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c118, c146, c141, c37, c273, c855, c221, c275, c356, c582, c274, c860, c859, c465, c462, c846, c219, c226] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c855 := derived855 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c582 := derived582 a h
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c860 := derived860 a h
  have h12 : Entails.eval a c859 := derived859 a h
  have h13 : Entails.eval a c465 := derived465 a h
  have h14 : Entails.eval a c462 := derived462 a h
  have h15 : Entails.eval a c846 := derived846 a h
  have h16 : Entails.eval a c219 := h 218 (by decide)
  have h17 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c861, some c317, some c275, some c318, some c141, some c37, some c462, some c172, some c201, some c203, some c170, some c159, some c359, some c320, some c274, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c146, c861, c317, c275, c318, c141, c37, c462, c172, c201, c203, c170, c159, c359, c320, c274] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c861 := derived861 a h
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c462 := derived462 a h
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c359 := h 358 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨20, by decide⟩, false), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c862, some c146, some c861, some c317, some c275, some c118, some c215, some c318, some c141, some c37, some c274, some c166, some c860, some c859, some c773, some c114, some c204, some c5, some c157, some c19, some c203, some c4, some c271, some c858, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c862, c146, c861, c317, c275, c118, c215, c318, c141, c37, c274, c166, c860, c859, c773, c114, c204, c5, c157, c19, c203, c4, c271, c858] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c862 := derived862 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c861 := derived861 a h
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c166 := h 165 (by decide)
  have h12 : Entails.eval a c860 := derived860 a h
  have h13 : Entails.eval a c859 := derived859 a h
  have h14 : Entails.eval a c773 := derived773 a h
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c5 := h 4 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c4 := h 3 (by decide)
  have h22 : Entails.eval a c271 := h 270 (by decide)
  have h23 : Entails.eval a c858 := derived858 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c146, some c356, some c360, some c773, some c170, some c1, some c74, some c106, some c109, some c61, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c118, c146, c356, c360, c773, c170, c1, c74, c106, c109, c61] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c360 := h 359 (by decide)
  have h4 : Entails.eval a c773 := derived773 a h
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c141, some c37, some c146, some c118, some c861, some c317, some c318, some c275, some c862, some c864, some c274, some c166, some c863, some c860, some c786, some c19, some c70, some c106, some c33, some c848, some c765, some c35, some c41, some c218, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c141, c37, c146, c118, c861, c317, c318, c275, c862, c864, c274, c166, c863, c860, c786, c19, c70, c106, c33, c848, c765, c35, c41, c218] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c861 := derived861 a h
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c862 := derived862 a h
  have h9 : Entails.eval a c864 := derived864 a h
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c166 := h 165 (by decide)
  have h12 : Entails.eval a c863 := derived863 a h
  have h13 : Entails.eval a c860 := derived860 a h
  have h14 : Entails.eval a c786 := derived786 a h
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c848 := derived848 a h
  have h20 : Entails.eval a c765 := derived765 a h
  have h21 : Entails.eval a c35 := h 34 (by decide)
  have h22 : Entails.eval a c41 := h 40 (by decide)
  have h23 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨32, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c141, some c513, some c351, some c844, some c20, some c32, some c349, some c48, some c316, some c274, some c307, some c841, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c37, c141, c513, c351, c844, c20, c32, c349, c48, c316, c274, c307, c841] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨37, by decide⟩, true), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c111, some c68, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c108, c111, c68] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c141, some c513, some c351, some c275, some c309, some c349, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c37, c141, c513, c351, c275, c309, c349] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨32, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c141, some c513, some c844, some c358, some c107, some c106, some c50, some c866, some c868, some c316, some c274, some c58, some c360, some c867, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c37, c141, c513, c844, c358, c107, c106, c50, c866, c868, c316, c274, c58, c360, c867] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c844 := derived844 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c866 := derived866 a h
  have h9 : Entails.eval a c868 := derived868 a h
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c867 := derived867 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c666, some c18, some c5, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c214, c666, c18, c5] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c666 := derived666 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨24, by decide⟩, false), (⟨37, by decide⟩, true), (⟨14, by decide⟩, true), (⟨30, by decide⟩, true), (⟨34, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c164, some c270, some c1, some c201, some c140, some c160, some c797, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c114, c164, c270, c1, c201, c140, c160, c797] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c164 := h 163 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c797 := derived797 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨30, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c867, some c20, some c33, some c871, some c5, some c204, some c18, some c124, some c270, some c333, some c126, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c867, c20, c33, c871, c5, c204, c18, c124, c270, c333, c126] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c867 := derived867 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c871 := derived871 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨35, by decide⟩, false), (⟨30, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c872, some c359, some c116, some c20, some c9, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c872, c359, c116, c20, c9] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c872 := derived872 a h
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c37, some c141, some c513, some c844, some c358, some c106, some c2, some c59, some c154, some c873, some c870, some c275, some c61, some c359, some c867, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c274, c37, c141, c513, c844, c358, c106, c2, c59, c154, c873, c870, c275, c61, c359, c867] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c844 := derived844 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c873 := derived873 a h
  have h11 : Entails.eval a c870 := derived870 a h
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c867 := derived867 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c141, some c513, some c844, some c358, some c874, some c50, some c58, some c351, some c868, some c52, some c307, some c107, some c4, some c155, some c870, some c869, some c69, some c108, some c5, some c20, some c165, some c349, some c195, some c100, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c37, c141, c513, c844, c358, c874, c50, c58, c351, c868, c52, c307, c107, c4, c155, c870, c869, c69, c108, c5, c20, c165, c349, c195, c100] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c844 := derived844 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c874 := derived874 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c868 := derived868 a h
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c870 := derived870 a h
  have h16 : Entails.eval a c869 := derived869 a h
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c108 := h 107 (by decide)
  have h19 : Entails.eval a c5 := h 4 (by decide)
  have h20 : Entails.eval a c20 := h 19 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  have h24 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c18, some c5, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c114, c18, c5] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨33, by decide⟩, true), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c216, some c875, some c61, some c316, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c33, c216, c875, c61, c316] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c875 := derived875 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c876, some c141, some c273, some c877, some c9, some c111, some c867, some c116, some c124, some c359, some c333, some c85, some c274, some c213, some c226, some c242, some c266, some c137, some c35, some c203, some c265, some c136, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c876, c141, c273, c877, c9, c111, c867, c116, c124, c359, c333, c85, c274, c213, c226, c242, c266, c137, c35, c203, c265, c136] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c876 := derived876 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c877 := derived877 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c867 := derived867 a h
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c213 := h 212 (by decide)
  have h14 : Entails.eval a c226 := h 225 (by decide)
  have h15 : Entails.eval a c242 := h 241 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c203 := h 202 (by decide)
  have h20 : Entails.eval a c265 := h 264 (by decide)
  have h21 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c876, some c878, some c354, some c44, some c24, some c216, some c38, some c142, some c5, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c876, c878, c354, c44, c24, c216, c38, c142, c5] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c876 := derived876 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, true), (⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c108, some c75, some c276, some c112, some c319, some c320, some c60, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c38, c108, c75, c276, c112, c319, c320, c60] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c276 := h 275 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c319 := h 318 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨22, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c142, some c880, some c359, some c353, some c115, some c167, some c277, some c219, some c320, some c23, some c206, some c112, some c126, some c541, some c49, some c333, some c348, some c337, some c363, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c142, c880, c359, c353, c115, c167, c277, c219, c320, c23, c206, c112, c126, c541, c49, c333, c348, c337, c363] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c142 := h 141 (by decide)
  have h1 : Entails.eval a c880 := derived880 a h
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c541 := derived541 a h
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨36, by decide⟩, false), (⟨30, by decide⟩, true), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c844, some c273, some c142, some c38, some c881, some c143, some c154, some c150, some c359, some c206, some c7, some c469, some c50, some c45, some c338, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c844, c273, c142, c38, c881, c143, c154, c150, c359, c206, c7, c469, c50, c45, c338] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c881 := derived881 a h
  have h5 : Entails.eval a c143 := h 142 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c469 := derived469 a h
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c8, some c50, some c148, some c338, some c45, some c107, some c442, some c64, some c224, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c110, c8, c50, c148, c338, c45, c107, c442, c64, c224] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c338 := h 337 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c442 := derived442 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived883

end CochromaticTwenty.Certificates.B16_4_2
