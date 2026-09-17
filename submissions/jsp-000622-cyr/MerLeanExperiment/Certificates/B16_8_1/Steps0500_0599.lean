import MerLeanExperiment.Certificates.B16_8_1.Steps0400_0499

/-! Generated from the actual pinned b16_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c789 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c785, some c777, some c104, some c266, some c265, some c57, some c111, some c786, some c284, some c756, some c68, some c122, some c270, some c79, some c81, some c788, some c82, some c63, some c424, some c532, some c118, some c119, some c141, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c763, c785, c777, c104, c266, c265, c57, c111, c786, c284, c756, c68, c122, c270, c79, c81, c788, c82, c63, c424, c532, c118, c119, c141] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c786 := derived786 a h
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c756 := derived756 a h
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c788 := derived788 a h
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c63 := h 62 (by decide)
  have h19 : Entails.eval a c424 := derived424 a h
  have h20 : Entails.eval a c532 := derived532 a h
  have h21 : Entails.eval a c118 := h 117 (by decide)
  have h22 : Entails.eval a c119 := h 118 (by decide)
  have h23 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c51, some c263, some c787, some c421, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c763, c51, c263, c787, c421] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c421 := derived421 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c785, some c777, some c51, some c790, some c266, some c458, some c461, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c763, c785, c777, c51, c790, c266, c458, c461] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c790 := derived790 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c458 := derived458 a h
  have h7 : Entails.eval a c461 := derived461 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c458, some c461, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c763, c458, c461] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c458 := derived458 a h
  have h2 : Entails.eval a c461 := derived461 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c793 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c479, some c80, some c82, some c17, some c131, some c566, some c567, some c144, some c169, some c170, some c95, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked793 : lratChecker f793 p793 = .success := by decide +kernel
theorem unsat793 : Unsatisfiable (PosFin 57) f793 := by
  apply lratCheckerSound f793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p793
  · intro a ha; simp [p793] at ha; subst a; trivial
  · exact checked793
theorem derived793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c793 := by
  apply localUnsat_implies_entails f793 [c763, c479, c80, c82, c17, c131, c566, c567, c144, c169, c170, c95] c793 unsat793 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c479 := derived479 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c566 := derived566 a h
  have h7 : Entails.eval a c567 := derived567 a h
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c169 := h 168 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c794 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c771, some c72, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked794 : lratChecker f794 p794 = .success := by decide +kernel
theorem unsat794 : Unsatisfiable (PosFin 57) f794 := by
  apply lratCheckerSound f794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p794
  · intro a ha; simp [p794] at ha; subst a; trivial
  · exact checked794
theorem derived794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c794 := by
  apply localUnsat_implies_entails f794 [c771, c72] c794 unsat794 (by rfl) a
  have h0 : Entails.eval a c771 := derived771 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c795 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c792, some c58, some c479, some c79, some c82, some c80, some c284, some c75, some c641, some c472, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked795 : lratChecker f795 p795 = .success := by decide +kernel
theorem unsat795 : Unsatisfiable (PosFin 57) f795 := by
  apply lratCheckerSound f795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p795
  · intro a ha; simp [p795] at ha; subst a; trivial
  · exact checked795
theorem derived795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c795 := by
  apply localUnsat_implies_entails f795 [c763, c792, c58, c479, c79, c82, c80, c284, c75, c641, c472] c795 unsat795 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c792 := derived792 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c479 := derived479 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c641 := derived641 a h
  have h10 : Entails.eval a c472 := derived472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c796 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c777, some c279, some c791, some c785, some c284, some c794, some c795, some c792, some c58, some c139, some c779, some c793, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked796 : lratChecker f796 p796 = .success := by decide +kernel
theorem unsat796 : Unsatisfiable (PosFin 57) f796 := by
  apply lratCheckerSound f796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p796
  · intro a ha; simp [p796] at ha; subst a; trivial
  · exact checked796
theorem derived796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c796 := by
  apply localUnsat_implies_entails f796 [c763, c777, c279, c791, c785, c284, c794, c795, c792, c58, c139, c779, c793] c796 unsat796 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c791 := derived791 a h
  have h4 : Entails.eval a c785 := derived785 a h
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c794 := derived794 a h
  have h7 : Entails.eval a c795 := derived795 a h
  have h8 : Entails.eval a c792 := derived792 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c779 := derived779 a h
  have h12 : Entails.eval a c793 := derived793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c797 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c785, some c789, some c279, some c791, some c284, some c794, some c777, some c792, some c58, some c112, some c80, some c82, some c796, some c128, some c536, some c140, some c141, some c566, some c567, some c144, some c169, some c170, some c95, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked797 : lratChecker f797 p797 = .success := by decide +kernel
theorem unsat797 : Unsatisfiable (PosFin 57) f797 := by
  apply lratCheckerSound f797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p797
  · intro a ha; simp [p797] at ha; subst a; trivial
  · exact checked797
theorem derived797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c797 := by
  apply localUnsat_implies_entails f797 [c763, c785, c789, c279, c791, c284, c794, c777, c792, c58, c112, c80, c82, c796, c128, c536, c140, c141, c566, c567, c144, c169, c170, c95] c797 unsat797 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c789 := derived789 a h
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c791 := derived791 a h
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c794 := derived794 a h
  have h7 : Entails.eval a c777 := derived777 a h
  have h8 : Entails.eval a c792 := derived792 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c796 := derived796 a h
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c536 := derived536 a h
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c566 := derived566 a h
  have h19 : Entails.eval a c567 := derived567 a h
  have h20 : Entails.eval a c144 := h 143 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  have h22 : Entails.eval a c170 := h 169 (by decide)
  have h23 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c798 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c82, some c348, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked798 : lratChecker f798 p798 = .success := by decide +kernel
theorem unsat798 : Unsatisfiable (PosFin 57) f798 := by
  apply lratCheckerSound f798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p798
  · intro a ha; simp [p798] at ha; subst a; trivial
  · exact checked798
theorem derived798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c798 := by
  apply localUnsat_implies_entails f798 [c82, c348] c798 unsat798 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c348 := derived348 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c799 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c785, some c777, some c789, some c279, some c791, some c284, some c794, some c797, some c266, some c265, some c57, some c263, some c267, some c798, some c471, some c89, some c54, some c314, some c312, some c466, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c763, c785, c777, c789, c279, c791, c284, c794, c797, c266, c265, c57, c263, c267, c798, c471, c89, c54, c314, c312, c466] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c777 := derived777 a h
  have h3 : Entails.eval a c789 := derived789 a h
  have h4 : Entails.eval a c279 := h 278 (by decide)
  have h5 : Entails.eval a c791 := derived791 a h
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c794 := derived794 a h
  have h8 : Entails.eval a c797 := derived797 a h
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c798 := derived798 a h
  have h15 : Entails.eval a c471 := derived471 a h
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c54 := h 53 (by decide)
  have h18 : Entails.eval a c314 := derived314 a h
  have h19 : Entails.eval a c312 := derived312 a h
  have h20 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c777, some c265, some c266, some c799, some c785, some c791, some c263, some c284, some c267, some c778, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c777, c265, c266, c799, c785, c791, c263, c284, c267, c778] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c777 := derived777 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c799 := derived799 a h
  have h4 : Entails.eval a c785 := derived785 a h
  have h5 : Entails.eval a c791 := derived791 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c778 := derived778 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c799, some c785, some c777, some c266, some c57, some c111, some c135, some c5, some c800, some c279, some c739, some c68, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c763, c799, c785, c777, c266, c57, c111, c135, c5, c800, c279, c739, c68] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c799 := derived799 a h
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c777 := derived777 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c800 := derived800 a h
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c739 := derived739 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c777, some c785, some c799, some c801, some c792, some c51, some c58, some c285, some c284, some c794, some c479, some c3, some c5, some c130, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c763, c777, c785, c799, c801, c792, c51, c58, c285, c284, c794, c479, c3, c5, c130] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c785 := derived785 a h
  have h3 : Entails.eval a c799 := derived799 a h
  have h4 : Entails.eval a c801 := derived801 a h
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c794 := derived794 a h
  have h11 : Entails.eval a c479 := derived479 a h
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c76, some c479, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c763, c76, c479] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c479 := derived479 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c792, some c802, some c51, some c283, some c58, some c803, some c688, some c112, some c536, some c139, some c104, some c795, some c793, some c17, some c141, some c130, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c763, c792, c802, c51, c283, c58, c803, c688, c112, c536, c139, c104, c795, c793, c17, c141, c130] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c792 := derived792 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c803 := derived803 a h
  have h7 : Entails.eval a c688 := derived688 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c536 := derived536 a h
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c795 := derived795 a h
  have h13 : Entails.eval a c793 := derived793 a h
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c792, some c51, some c283, some c282, some c58, some c803, some c688, some c112, some c536, some c804, some c74, some c17, some c130, some c131, some c141, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c763, c802, c792, c51, c283, c282, c58, c803, c688, c112, c536, c804, c74, c17, c130, c131, c141] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c803 := derived803 a h
  have h8 : Entails.eval a c688 := derived688 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c536 := derived536 a h
  have h11 : Entails.eval a c804 := derived804 a h
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c677, some c203, some c25, some c241, some c240, some c44, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c763, c677, c203, c25, c241, c240, c44] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c677 := derived677 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c240 := h 239 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c792, some c51, some c58, some c282, some c805, some c280, some c671, some c60, some c79, some c81, some c806, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c763, c802, c792, c51, c58, c282, c805, c280, c671, c60, c79, c81, c806] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c792 := derived792 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c805 := derived805 a h
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c671 := derived671 a h
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c806 := derived806 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c280, some c50, some c802, some c521, some c806, some c79, some c78, some c478, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c763, c280, c50, c802, c521, c806, c79, c78, c478] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c521 := derived521 a h
  have h5 : Entails.eval a c806 := derived806 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c478 := derived478 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c273, some c276, some c60, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c763, c273, c276, c60] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c521, some c203, some c209, some c34, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c763, c521, c203, c209, c34] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c521 := derived521 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c807, some c802, some c521, some c280, some c287, some c104, some c50, some c256, some c808, some c2, some c80, some c81, some c55, some c809, some c115, some c1, some c810, some c26, some c240, some c246, some c43, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c763, c807, c802, c521, c280, c287, c104, c50, c256, c808, c2, c80, c81, c55, c809, c115, c1, c810, c26, c240, c246, c43] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c808 := derived808 a h
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c809 := derived809 a h
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c810 := derived810 a h
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c240 := h 239 (by decide)
  have h20 : Entails.eval a c246 := h 245 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c463, some c464, some c466, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c763, c802, c463, c464, c466] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c464 := derived464 a h
  have h4 : Entails.eval a c466 := derived466 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c12, some c131, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c13, c12, c131] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c74, some c630, some c813, some c115, some c15, some c16, some c130, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c89, c74, c630, c813, c115, c15, c16, c130] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c630 := derived630 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨27, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c277, some c89, some c81, some c26, some c814, some c501, some c180, some c247, some c236, some c42, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c802, c277, c89, c81, c26, c814, c501, c180, c247, c236, c42] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c814 := derived814 a h
  have h6 : Entails.eval a c501 := derived501 a h
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c41, some c42, some c226, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c763, c41, c42, c226] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c811, some c803, some c807, some c802, some c81, some c89, some c50, some c58, some c59, some c272, some c816, some c235, some c815, some c198, some c33, some c32, some c189, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c763, c811, c803, c807, c802, c81, c89, c50, c58, c59, c272, c816, c235, c815, c198, c33, c32, c189] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c811 := derived811 a h
  have h2 : Entails.eval a c803 := derived803 a h
  have h3 : Entails.eval a c807 := derived807 a h
  have h4 : Entails.eval a c802 := derived802 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c816 := derived816 a h
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c815 := derived815 a h
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c32 := h 31 (by decide)
  have h17 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c272, some c61, some c79, some c816, some c236, some c27, some c199, some c33, some c32, some c189, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c763, c272, c61, c79, c816, c236, c27, c199, c33, c32, c189] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c816 := derived816 a h
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c51, some c58, some c282, some c622, some c74, some c82, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c763, c802, c51, c58, c282, c622, c74, c82] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c622 := derived622 a h
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨35, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c817, some c811, some c803, some c807, some c802, some c819, some c818, some c54, some c415, some c627, some c26, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c817, c811, c803, c807, c802, c819, c818, c54, c415, c627, c26] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c817 := derived817 a h
  have h1 : Entails.eval a c811 := derived811 a h
  have h2 : Entails.eval a c803 := derived803 a h
  have h3 : Entails.eval a c807 := derived807 a h
  have h4 : Entails.eval a c802 := derived802 a h
  have h5 : Entails.eval a c819 := derived819 a h
  have h6 : Entails.eval a c818 := derived818 a h
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c415 := derived415 a h
  have h9 : Entails.eval a c627 := derived627 a h
  have h10 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c17, some c130, some c131, some c141, some c124, some c724, some c282, some c261, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c113, c17, c130, c131, c141, c124, c724, c282, c261] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c724 := derived724 a h
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c277, some c817, some c811, some c803, some c807, some c820, some c88, some c61, some c26, some c44, some c664, some c198, some c24, some c688, some c821, some c540, some c203, some c241, some c25, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c763, c802, c277, c817, c811, c803, c807, c820, c88, c61, c26, c44, c664, c198, c24, c688, c821, c540, c203, c241, c25] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c817 := derived817 a h
  have h4 : Entails.eval a c811 := derived811 a h
  have h5 : Entails.eval a c803 := derived803 a h
  have h6 : Entails.eval a c807 := derived807 a h
  have h7 : Entails.eval a c820 := derived820 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c664 := derived664 a h
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c688 := derived688 a h
  have h16 : Entails.eval a c821 := derived821 a h
  have h17 : Entails.eval a c540 := derived540 a h
  have h18 : Entails.eval a c203 := h 202 (by decide)
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨55, by decide⟩, true), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c807, some c817, some c811, some c803, some c88, some c61, some c272, some c540, some c276, some c58, some c111, some c263, some c688, some c17, some c724, some c536, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c763, c807, c817, c811, c803, c88, c61, c272, c540, c276, c58, c111, c263, c688, c17, c724, c536] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c817 := derived817 a h
  have h3 : Entails.eval a c811 := derived811 a h
  have h4 : Entails.eval a c803 := derived803 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c540 := derived540 a h
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c688 := derived688 a h
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c724 := derived724 a h
  have h16 : Entails.eval a c536 := derived536 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c802, some c822, some c235, some c277, some c817, some c811, some c803, some c807, some c88, some c61, some c823, some c821, some c688, some c58, some c41, some c24, some c225, some c199, some c27, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c763, c802, c822, c235, c277, c817, c811, c803, c807, c88, c61, c823, c821, c688, c58, c41, c24, c225, c199, c27] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c822 := derived822 a h
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c817 := derived817 a h
  have h6 : Entails.eval a c811 := derived811 a h
  have h7 : Entails.eval a c803 := derived803 a h
  have h8 : Entails.eval a c807 := derived807 a h
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c823 := derived823 a h
  have h12 : Entails.eval a c821 := derived821 a h
  have h13 : Entails.eval a c688 := derived688 a h
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c41 := h 40 (by decide)
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c225 := h 224 (by decide)
  have h18 : Entails.eval a c199 := h 198 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c817, some c811, some c803, some c807, some c802, some c822, some c824, some c819, some c818, some c54, some c415, some c244, some c627, some c28, some c35, some c210, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c817, c811, c803, c807, c802, c822, c824, c819, c818, c54, c415, c244, c627, c28, c35, c210] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c817 := derived817 a h
  have h1 : Entails.eval a c811 := derived811 a h
  have h2 : Entails.eval a c803 := derived803 a h
  have h3 : Entails.eval a c807 := derived807 a h
  have h4 : Entails.eval a c802 := derived802 a h
  have h5 : Entails.eval a c822 := derived822 a h
  have h6 : Entails.eval a c824 := derived824 a h
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c818 := derived818 a h
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c415 := derived415 a h
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c627 := derived627 a h
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c807, some c811, some c803, some c817, some c825, some c104, some c50, some c688, some c79, some c283, some c61, some c754, some c701, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c802, c807, c811, c803, c817, c825, c104, c50, c688, c79, c283, c61, c754, c701] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c807 := derived807 a h
  have h2 : Entails.eval a c811 := derived811 a h
  have h3 : Entails.eval a c803 := derived803 a h
  have h4 : Entails.eval a c817 := derived817 a h
  have h5 : Entails.eval a c825 := derived825 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c688 := derived688 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c754 := derived754 a h
  have h13 : Entails.eval a c701 := derived701 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c826, some c279, some c285, some c104, some c50, some c51, some c480, some c79, some c81, some c792, some c61, some c273, some c701, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c763, c826, c279, c285, c104, c50, c51, c480, c79, c81, c792, c61, c273, c701] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c826 := derived826 a h
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c480 := derived480 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c792 := derived792 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  have h13 : Entails.eval a c701 := derived701 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c68, some c81, some c79, some c51, some c61, some c267, some c540, some c268, some c701, some c336, some c334, some c111, some c122, some c65, some c17, some c118, some c119, some c141, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c763, c68, c81, c79, c51, c61, c267, c540, c268, c701, c336, c334, c111, c122, c65, c17, c118, c119, c141] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c701 := derived701 a h
  have h10 : Entails.eval a c336 := derived336 a h
  have h11 : Entails.eval a c334 := derived334 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c407, some c413, some c25, some c161, some c160, some c225, some c224, some c157, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c763, c407, c413, c25, c161, c160, c225, c224, c157] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c413 := derived413 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c225 := h 224 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c827, some c802, some c521, some c51, some c68, some c79, some c81, some c828, some c271, some c266, some c111, some c5, some c122, some c788, some c798, some c829, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c763, c827, c802, c521, c51, c68, c79, c81, c828, c271, c266, c111, c5, c122, c788, c798, c829] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c828 := derived828 a h
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c788 := derived788 a h
  have h15 : Entails.eval a c798 := derived798 a h
  have h16 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c88, some c69, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c79, c88, c69] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c55, some c610, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c267, c55, c610] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c610 := derived610 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c802, some c283, some c282, some c827, some c806, some c832, some c61, some c671, some c265, some c264, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c285, c802, c283, c282, c827, c806, c832, c61, c671, c265, c264] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c827 := derived827 a h
  have h5 : Entails.eval a c806 := derived806 a h
  have h6 : Entails.eval a c832 := derived832 a h
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c671 := derived671 a h
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c830, some c282, some c831, some c833, some c81, some c89, some c69, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c802, c830, c282, c831, c833, c81, c89, c69] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c830 := derived830 a h
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c831 := derived831 a h
  have h4 : Entails.eval a c833 := derived833 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c816, some c235, some c26, some c198, some c33, some c32, some c189, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c763, c816, c235, c26, c198, c33, c32, c189] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c816 := derived816 a h
  have h2 : Entails.eval a c235 := h 234 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c207, some c33, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c198, c207, c33] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c835, some c54, some c836, some c26, some c235, some c244, some c42, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c835, c54, c836, c26, c235, c244, c42] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c835 := derived835 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c836 := derived836 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c235 := h 234 (by decide)
  have h5 : Entails.eval a c244 := h 243 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c235, some c244, some c42, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c235, c244, c42] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c235 := h 234 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c501, some c836, some c838, some c180, some c236, some c247, some c42, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c802, c501, c836, c838, c180, c236, c247, c42] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c501 := derived501 a h
  have h2 : Entails.eval a c836 := derived836 a h
  have h3 : Entails.eval a c838 := derived838 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c834, some c279, some c802, some c277, some c278, some c81, some c89, some c812, some c51, some c837, some c839, some c54, some c270, some c272, some c814, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c763, c834, c279, c802, c277, c278, c81, c89, c812, c51, c837, c839, c54, c270, c272, c814] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c812 := derived812 a h
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c837 := derived837 a h
  have h11 : Entails.eval a c839 := derived839 a h
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c814 := derived814 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨42, by decide⟩, false), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c840, some c834, some c54, some c270, some c818, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c840, c834, c54, c270, c818] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c840 := derived840 a h
  have h1 : Entails.eval a c834 := derived834 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c840, some c834, some c802, some c471, some c51, some c841, some c88, some c664, some c24, some c199, some c198, some c35, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c763, c840, c834, c802, c471, c51, c841, c88, c664, c24, c199, c198, c35] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c834 := derived834 a h
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c471 := derived471 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c664 := derived664 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c270, some c272, some c61, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c270, c272, c61] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c261, some c262, some c274, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c843, c261, c262, c274] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c827, some c802, some c419, some c261, some c269, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c827, c802, c419, c261, c269] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c827 := derived827 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c419 := derived419 a h
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c269, some c61, some c263, some c268, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c265, c269, c61, c263, c268] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c840, some c834, some c279, some c802, some c277, some c278, some c827, some c842, some c79, some c844, some c51, some c845, some c846, some c264, some c275, some c268, some c61, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c763, c840, c834, c279, c802, c277, c278, c827, c842, c79, c844, c51, c845, c846, c264, c275, c268, c61] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c834 := derived834 a h
  have h3 : Entails.eval a c279 := h 278 (by decide)
  have h4 : Entails.eval a c802 := derived802 a h
  have h5 : Entails.eval a c277 := h 276 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c827 := derived827 a h
  have h8 : Entails.eval a c842 := derived842 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c844 := derived844 a h
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c845 := derived845 a h
  have h13 : Entails.eval a c846 := derived846 a h
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c275 := h 274 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c847, some c840, some c802, some c834, some c277, some c278, some c827, some c264, some c266, some c268, some c61, some c341, some c88, some c839, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c847, c840, c802, c834, c277, c278, c827, c264, c266, c268, c61, c341, c88, c839] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c847 := derived847 a h
  have h1 : Entails.eval a c840 := derived840 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c834 := derived834 a h
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c827 := derived827 a h
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c341 := derived341 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c839 := derived839 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c827, some c802, some c834, some c278, some c279, some c840, some c847, some c848, some c846, some c79, some c88, some c839, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c827, c802, c834, c278, c279, c840, c847, c848, c846, c79, c88, c839] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c827 := derived827 a h
  have h1 : Entails.eval a c802 := derived802 a h
  have h2 : Entails.eval a c834 := derived834 a h
  have h3 : Entails.eval a c278 := h 277 (by decide)
  have h4 : Entails.eval a c279 := h 278 (by decide)
  have h5 : Entails.eval a c840 := derived840 a h
  have h6 : Entails.eval a c847 := derived847 a h
  have h7 : Entails.eval a c848 := derived848 a h
  have h8 : Entails.eval a c846 := derived846 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c839 := derived839 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c827, some c269, some c265, some c849, some c802, some c70, some c57, some c282, some c283, some c285, some c812, some c268, some c771, some c77, some c109, some c69, some c18, some c129, some c131, some c11, some c143, some c115, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c763, c827, c269, c265, c849, c802, c70, c57, c282, c283, c285, c812, c268, c771, c77, c109, c69, c18, c129, c131, c11, c143, c115] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c849 := derived849 a h
  have h5 : Entails.eval a c802 := derived802 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c812 := derived812 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c771 := derived771 a h
  have h14 : Entails.eval a c77 := h 76 (by decide)
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c143 := h 142 (by decide)
  have h22 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c849, some c802, some c521, some c476, some c27, some c249, some c241, some c43, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c763, c849, c802, c521, c476, c27, c249, c241, c43] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c476 := derived476 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c249 := h 248 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c849, some c851, some c70, some c850, some c812, some c833, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c763, c849, c851, c70, c850, c812, c833] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c851 := derived851 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c850 := derived850 a h
  have h5 : Entails.eval a c812 := derived812 a h
  have h6 : Entails.eval a c833 := derived833 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c849, some c827, some c802, some c851, some c70, some c283, some c285, some c852, some c77, some c846, some c78, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c763, c849, c827, c802, c851, c70, c283, c285, c852, c77, c846, c78] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c827 := derived827 a h
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c851 := derived851 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c852 := derived852 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c846 := derived846 a h
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c849, some c279, some c285, some c480, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c763, c849, c279, c285, c480] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c480 := derived480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c849, some c802, some c521, some c70, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c763, c849, c802, c521, c70] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c802 := derived802 a h
  have h3 : Entails.eval a c521 := derived521 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c853, some c827, some c269, some c854, some c55, some c80, some c855, some c812, some c109, some c15, some c265, some c802, some c283, some c282, some c849, some c77, some c610, some c18, some c115, some c129, some c131, some c142, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c853, c827, c269, c854, c55, c80, c855, c812, c109, c15, c265, c802, c283, c282, c849, c77, c610, c18, c115, c129, c131, c142] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c853 := derived853 a h
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c854 := derived854 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c855 := derived855 a h
  have h7 : Entails.eval a c812 := derived812 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c802 := derived802 a h
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c849 := derived849 a h
  have h15 : Entails.eval a c77 := h 76 (by decide)
  have h16 : Entails.eval a c610 := derived610 a h
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c115 := h 114 (by decide)
  have h19 : Entails.eval a c129 := h 128 (by decide)
  have h20 : Entails.eval a c131 := h 130 (by decide)
  have h21 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c855, some c849, some c802, some c246, some c240, some c43, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c763, c855, c849, c802, c246, c240, c43] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c240 := h 239 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c855, some c849, some c802, some c476, some c810, some c857, some c180, some c249, some c241, some c43, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c763, c855, c849, c802, c476, c810, c857, c180, c249, c241, c43] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c802 := derived802 a h
  have h4 : Entails.eval a c476 := derived476 a h
  have h5 : Entails.eval a c810 := derived810 a h
  have h6 : Entails.eval a c857 := derived857 a h
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c249 := h 248 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c802, some c827, some c849, some c854, some c855, some c282, some c283, some c858, some c57, some c76, some c77, some c856, some c266, some c268, some c110, some c18, some c130, some c128, some c772, some c143, some c115, some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c802, c827, c849, c854, c855, c282, c283, c858, c57, c76, c77, c856, c266, c268, c110, c18, c130, c128, c772, c143, c115] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c802 := derived802 a h
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c854 := derived854 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c858 := derived858 a h
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c856 := derived856 a h
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c130 := h 129 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  have h18 : Entails.eval a c772 := derived772 a h
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c283, some c419, some c260, some c276, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c859, c283, c419, c260, c276] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c419 := derived419 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨27, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, false), (⟨41, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c26, some c456, some c78, some c58, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c763, c26, c456, c78, c58] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c456 := derived456 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, true), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c251, some c231, some c41, some c52, some c78, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c763, c251, c231, c41, c52, c78] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c297, some c78, some c12, some c58, some c106, some c293, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c859, c763, c297, c78, c12, c58, c106, c293] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c297 := derived297 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c293 := derived293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨44, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c57, some c297, some c70, some c25, some c43, some c862, some c861, some c863, some c52, some c71, some c403, some c404, some c194, some c205, some c40, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c763, c859, c57, c297, c70, c25, c43, c862, c861, c863, c52, c71, c403, c404, c194, c205, c40] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c862 := derived862 a h
  have h8 : Entails.eval a c861 := derived861 a h
  have h9 : Entails.eval a c863 := derived863 a h
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c403 := derived403 a h
  have h13 : Entails.eval a c404 := derived404 a h
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c57, some c297, some c70, some c863, some c52, some c71, some c403, some c404, some c194, some c34, some c40, some c205, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c859, c763, c57, c297, c70, c863, c52, c71, c403, c404, c194, c34, c40, c205] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c863 := derived863 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c403 := derived403 a h
  have h9 : Entails.eval a c404 := derived404 a h
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c57, some c297, some c70, some c52, some c71, some c403, some c404, some c231, some c242, some c49, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c763, c859, c57, c297, c70, c52, c71, c403, c404, c231, c242, c49] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c403 := derived403 a h
  have h8 : Entails.eval a c404 := derived404 a h
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c242 := h 241 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c57, some c70, some c860, some c297, some c77, some c110, some c260, some c864, some c865, some c861, some c866, some c78, some c12, some c58, some c106, some c295, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c859, c763, c57, c70, c860, c297, c77, c110, c260, c864, c865, c861, c866, c78, c12, c58, c106, c295] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c860 := derived860 a h
  have h5 : Entails.eval a c297 := derived297 a h
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c864 := derived864 a h
  have h10 : Entails.eval a c865 := derived865 a h
  have h11 : Entails.eval a c861 := derived861 a h
  have h12 : Entails.eval a c866 := derived866 a h
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c295 := derived295 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c485, some c492, some c405, some c416, some c273, some c443, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c859, c485, c492, c405, c416, c273, c443] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c485 := derived485 a h
  have h2 : Entails.eval a c492 := derived492 a h
  have h3 : Entails.eval a c405 := derived405 a h
  have h4 : Entails.eval a c416 := derived416 a h
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c443 := derived443 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c57, some c70, some c860, some c297, some c867, some c397, some c403, some c76, some c868, some c58, some c82, some c481, some c80, some c63, some c112, some c276, some c405, some c416, some c11, some c139, some c125, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c763, c859, c57, c70, c860, c297, c867, c397, c403, c76, c868, c58, c82, c481, c80, c63, c112, c276, c405, c416, c11, c139, c125] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c860 := derived860 a h
  have h5 : Entails.eval a c297 := derived297 a h
  have h6 : Entails.eval a c867 := derived867 a h
  have h7 : Entails.eval a c397 := derived397 a h
  have h8 : Entails.eval a c403 := derived403 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c868 := derived868 a h
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c481 := derived481 a h
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c276 := h 275 (by decide)
  have h18 : Entails.eval a c405 := derived405 a h
  have h19 : Entails.eval a c416 := derived416 a h
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c139 := h 138 (by decide)
  have h22 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c397, some c76, some c57, some c276, some c297, some c869, some c70, some c82, some c481, some c80, some c335, some c112, some c483, some c113, some c137, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c763, c859, c397, c76, c57, c276, c297, c869, c70, c82, c481, c80, c335, c112, c483, c113, c137] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c397 := derived397 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c297 := derived297 a h
  have h7 : Entails.eval a c869 := derived869 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c481 := derived481 a h
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c335 := derived335 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c483 := derived483 a h
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c57, some c297, some c869, some c397, some c76, some c870, some c58, some c274, some c492, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c763, c859, c57, c297, c869, c397, c76, c870, c58, c274, c492] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c397 := derived397 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c870 := derived870 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c492 := derived492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨55, by decide⟩, true), (⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c50, some c58, some c59, some c274, some c271, some c52, some c106, some c259, some c12, some c11, some c556, some c131, some c113, some c135, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c763, c50, c58, c59, c274, c271, c52, c106, c259, c12, c11, c556, c131, c113, c135] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c556 := derived556 a h
  have h12 : Entails.eval a c131 := h 130 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨41, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c739, some c721, some c112, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c859, c739, c721, c112] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c721 := derived721 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c57, some c297, some c869, some c70, some c276, some c871, some c77, some c872, some c82, some c78, some c76, some c52, some c71, some c458, some c873, some c2, some c484, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c859, c763, c57, c297, c869, c70, c276, c871, c77, c872, c82, c78, c76, c52, c71, c458, c873, c2, c484] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c872 := derived872 a h
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c458 := derived458 a h
  have h16 : Entails.eval a c873 := derived873 a h
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c484 := derived484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c869, some c57, some c297, some c874, some c53, some c107, some c258, some c462, some c275, some c58, some c80, some c299, some c484, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c763, c859, c869, c57, c297, c874, c53, c107, c258, c462, c275, c58, c80, c299, c484] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c869 := derived869 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c297 := derived297 a h
  have h5 : Entails.eval a c874 := derived874 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c462 := derived462 a h
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c299 := derived299 a h
  have h14 : Entails.eval a c484 := derived484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c271, some c512, some c112, some c139, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c266, c271, c512, c112, c139] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c512 := derived512 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c70, some c875, some c283, some c77, some c82, some c78, some c76, some c517, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c763, c70, c875, c283, c77, c82, c78, c76, c517] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c875 := derived875 a h
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c517 := derived517 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨43, by decide⟩, true), (⟨9, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c877, some c70, some c875, some c283, some c77, some c869, some c104, some c58, some c464, some c463, some c274, some c489, some c146, some c26, some c518, some c171, some c168, some c131, some c90, some c12, some c141, some c116, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c763, c859, c877, c70, c875, c283, c77, c869, c104, c58, c464, c463, c274, c489, c146, c26, c518, c171, c168, c131, c90, c12, c141, c116] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c875 := derived875 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c869 := derived869 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c464 := derived464 a h
  have h11 : Entails.eval a c463 := derived463 a h
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c489 := derived489 a h
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c518 := derived518 a h
  have h17 : Entails.eval a c171 := h 170 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c90 := h 89 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c141 := h 140 (by decide)
  have h23 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c138, some c116, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c140, c138, c116] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c464, some c463, some c146, some c171, some c168, some c90, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c763, c464, c463, c146, c171, c168, c90] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c464 := derived464 a h
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c877, some c70, some c875, some c283, some c282, some c869, some c57, some c876, some c878, some c268, some c269, some c518, some c131, some c879, some c880, some c69, some c123, some c443, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c763, c859, c877, c70, c875, c283, c282, c869, c57, c876, c878, c268, c269, c518, c131, c879, c880, c69, c123, c443] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c875 := derived875 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c869 := derived869 a h
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c876 := derived876 a h
  have h10 : Entails.eval a c878 := derived878 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c518 := derived518 a h
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c879 := derived879 a h
  have h16 : Entails.eval a c880 := derived880 a h
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c123 := h 122 (by decide)
  have h19 : Entails.eval a c443 := derived443 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c877, some c875, some c57, some c881, some c107, some c268, some c104, some c58, some c489, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c859, c763, c877, c875, c57, c881, c107, c268, c104, c58, c489] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c875 := derived875 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c881 := derived881 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c489 := derived489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c877, some c875, some c57, some c268, some c50, some c58, some c489, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c763, c877, c875, c57, c268, c50, c58, c489] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c877 := derived877 a h
  have h2 : Entails.eval a c875 := derived875 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c489 := derived489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c271, some c116, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c274, c271, c116] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c70, some c57, some c869, some c875, some c283, some c877, some c882, some c883, some c107, some c518, some c134, some c131, some c132, some c884, some c58, some c266, some c269, some c116, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c763, c859, c70, c57, c869, c875, c283, c877, c882, c883, c107, c518, c134, c131, c132, c884, c58, c266, c269, c116] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c875 := derived875 a h
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c877 := derived877 a h
  have h8 : Entails.eval a c882 := derived882 a h
  have h9 : Entails.eval a c883 := derived883 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c518 := derived518 a h
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c132 := h 131 (by decide)
  have h15 : Entails.eval a c884 := derived884 a h
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c885, some c51, some c60, some c297, some c266, some c268, some c282, some c283, some c860, some c278, some c269, some c69, some c443, some c123, some c129, some c337, some c132, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c763, c859, c885, c51, c60, c297, c266, c268, c282, c283, c860, c278, c269, c69, c443, c123, c129, c337, c132] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c297 := derived297 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c860 := derived860 a h
  have h11 : Entails.eval a c278 := h 277 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c443 := derived443 a h
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c129 := h 128 (by decide)
  have h17 : Entails.eval a c337 := derived337 a h
  have h18 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c120, some c116, some c109, some c297, some c268, some c132, some c365, some c278, some c287, some c129, some c69, some c443, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c859, c120, c116, c109, c297, c268, c132, c365, c278, c287, c129, c69, c443] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c297 := derived297 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c365 := derived365 a h
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c287 := h 286 (by decide)
  have h10 : Entails.eval a c129 := h 128 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c443 := derived443 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c887, some c267, some c274, some c258, some c260, some c521, some c283, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c859, c887, c267, c274, c258, c260, c521, c283] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c887 := derived887 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c521 := derived521 a h
  have h7 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived888

end CochromaticTwenty.Certificates.B16_8_1
