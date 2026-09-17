import MerLeanExperiment.Certificates.FixedCore1.Steps2800_2899

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8781 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7664, some c7708, some c7711, some c7608, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8781 : lratChecker f8781 p8781 = .success := by decide +kernel
theorem unsat8781 : Unsatisfiable (PosFin 65) f8781 := by
  apply lratCheckerSound f8781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8781
  · intro a ha; simp [p8781] at ha; subst a; trivial
  · exact checked8781
theorem derived8781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8781 := by
  apply localUnsat_implies_entails f8781 [c7664, c7708, c7711, c7608] c8781 unsat8781 (by rfl) a
  have h0 : Entails.eval a c7664 := derived7664 a h
  have h1 : Entails.eval a c7708 := derived7708 a h
  have h2 : Entails.eval a c7711 := derived7711 a h
  have h3 : Entails.eval a c7608 := derived7608 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8782 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8780, some c8781, some c7466, some c7394, some c7439, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8782 : lratChecker f8782 p8782 = .success := by decide +kernel
theorem unsat8782 : Unsatisfiable (PosFin 65) f8782 := by
  apply lratCheckerSound f8782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8782
  · intro a ha; simp [p8782] at ha; subst a; trivial
  · exact checked8782
theorem derived8782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8782 := by
  apply localUnsat_implies_entails f8782 [c8780, c8781, c7466, c7394, c7439] c8782 unsat8782 (by rfl) a
  have h0 : Entails.eval a c8780 := derived8780 a h
  have h1 : Entails.eval a c8781 := derived8781 a h
  have h2 : Entails.eval a c7466 := derived7466 a h
  have h3 : Entails.eval a c7394 := derived7394 a h
  have h4 : Entails.eval a c7439 := derived7439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8783 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7559, some c7713, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p8783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8783 : lratChecker f8783 p8783 = .success := by decide +kernel
theorem unsat8783 : Unsatisfiable (PosFin 65) f8783 := by
  apply lratCheckerSound f8783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8783
  · intro a ha; simp [p8783] at ha; subst a; trivial
  · exact checked8783
theorem derived8783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8783 := by
  apply localUnsat_implies_entails f8783 [c7559, c7713] c8783 unsat8783 (by rfl) a
  have h0 : Entails.eval a c7559 := derived7559 a h
  have h1 : Entails.eval a c7713 := derived7713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8784 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8782, some c8780, some c7549, some c8783, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8784 : lratChecker f8784 p8784 = .success := by decide +kernel
theorem unsat8784 : Unsatisfiable (PosFin 65) f8784 := by
  apply lratCheckerSound f8784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8784
  · intro a ha; simp [p8784] at ha; subst a; trivial
  · exact checked8784
theorem derived8784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8784 := by
  apply localUnsat_implies_entails f8784 [c8782, c8780, c7549, c8783] c8784 unsat8784 (by rfl) a
  have h0 : Entails.eval a c8782 := derived8782 a h
  have h1 : Entails.eval a c8780 := derived8780 a h
  have h2 : Entails.eval a c7549 := derived7549 a h
  have h3 : Entails.eval a c8783 := derived8783 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8785 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8772, some c8761, some c8670, some c8780, some c8784, some c7394, some c7439, some c106, some c6747, some c6748, some c3116, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8785 : lratChecker f8785 p8785 = .success := by decide +kernel
theorem unsat8785 : Unsatisfiable (PosFin 65) f8785 := by
  apply lratCheckerSound f8785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8785
  · intro a ha; simp [p8785] at ha; subst a; trivial
  · exact checked8785
theorem derived8785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8785 := by
  apply localUnsat_implies_entails f8785 [c8772, c8761, c8670, c8780, c8784, c7394, c7439, c106, c6747, c6748, c3116] c8785 unsat8785 (by rfl) a
  have h0 : Entails.eval a c8772 := derived8772 a h
  have h1 : Entails.eval a c8761 := derived8761 a h
  have h2 : Entails.eval a c8670 := derived8670 a h
  have h3 : Entails.eval a c8780 := derived8780 a h
  have h4 : Entails.eval a c8784 := derived8784 a h
  have h5 : Entails.eval a c7394 := derived7394 a h
  have h6 : Entails.eval a c7439 := derived7439 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c6747 := derived6747 a h
  have h9 : Entails.eval a c6748 := derived6748 a h
  have h10 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8786 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7847, some c7825, some c7845, some c7753, some c7819, some c7827, some c726, some c739, some c734, some c729, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8786 : lratChecker f8786 p8786 = .success := by decide +kernel
theorem unsat8786 : Unsatisfiable (PosFin 65) f8786 := by
  apply lratCheckerSound f8786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8786
  · intro a ha; simp [p8786] at ha; subst a; trivial
  · exact checked8786
theorem derived8786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8786 := by
  apply localUnsat_implies_entails f8786 [c7847, c7825, c7845, c7753, c7819, c7827, c726, c739, c734, c729] c8786 unsat8786 (by rfl) a
  have h0 : Entails.eval a c7847 := derived7847 a h
  have h1 : Entails.eval a c7825 := derived7825 a h
  have h2 : Entails.eval a c7845 := derived7845 a h
  have h3 : Entails.eval a c7753 := derived7753 a h
  have h4 : Entails.eval a c7819 := derived7819 a h
  have h5 : Entails.eval a c7827 := derived7827 a h
  have h6 : Entails.eval a c726 := h 725 (by decide)
  have h7 : Entails.eval a c739 := h 738 (by decide)
  have h8 : Entails.eval a c734 := h 733 (by decide)
  have h9 : Entails.eval a c729 := h 728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8787 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8785, some c8772, some c8761, some c8786, some c7567, some c7568, some c7375, some c789, some c2623, some c1111, some c1142, some c1131, some c2547, some c2529, some c1143, some c2362, some c1838, some c2518, some c7716, some c1015, some c2075, some c7496, some c14, some c15, some c76, some c896, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked8787 : lratChecker f8787 p8787 = .success := by decide +kernel
theorem unsat8787 : Unsatisfiable (PosFin 65) f8787 := by
  apply lratCheckerSound f8787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8787
  · intro a ha; simp [p8787] at ha; subst a; trivial
  · exact checked8787
theorem derived8787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8787 := by
  apply localUnsat_implies_entails f8787 [c8785, c8772, c8761, c8786, c7567, c7568, c7375, c789, c2623, c1111, c1142, c1131, c2547, c2529, c1143, c2362, c1838, c2518, c7716, c1015, c2075, c7496, c14, c15, c76, c896] c8787 unsat8787 (by rfl) a
  have h0 : Entails.eval a c8785 := derived8785 a h
  have h1 : Entails.eval a c8772 := derived8772 a h
  have h2 : Entails.eval a c8761 := derived8761 a h
  have h3 : Entails.eval a c8786 := derived8786 a h
  have h4 : Entails.eval a c7567 := derived7567 a h
  have h5 : Entails.eval a c7568 := derived7568 a h
  have h6 : Entails.eval a c7375 := derived7375 a h
  have h7 : Entails.eval a c789 := h 788 (by decide)
  have h8 : Entails.eval a c2623 := h 2622 (by decide)
  have h9 : Entails.eval a c1111 := h 1110 (by decide)
  have h10 : Entails.eval a c1142 := h 1141 (by decide)
  have h11 : Entails.eval a c1131 := h 1130 (by decide)
  have h12 : Entails.eval a c2547 := h 2546 (by decide)
  have h13 : Entails.eval a c2529 := h 2528 (by decide)
  have h14 : Entails.eval a c1143 := h 1142 (by decide)
  have h15 : Entails.eval a c2362 := h 2361 (by decide)
  have h16 : Entails.eval a c1838 := h 1837 (by decide)
  have h17 : Entails.eval a c2518 := h 2517 (by decide)
  have h18 : Entails.eval a c7716 := derived7716 a h
  have h19 : Entails.eval a c1015 := h 1014 (by decide)
  have h20 : Entails.eval a c2075 := h 2074 (by decide)
  have h21 : Entails.eval a c7496 := derived7496 a h
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c76 := h 75 (by decide)
  have h25 : Entails.eval a c896 := h 895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8788 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7467, some c7388, some c7390, some c7391, some c7323, some c7382, some c7352, some c7846, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8788 : lratChecker f8788 p8788 = .success := by decide +kernel
theorem unsat8788 : Unsatisfiable (PosFin 65) f8788 := by
  apply lratCheckerSound f8788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8788
  · intro a ha; simp [p8788] at ha; subst a; trivial
  · exact checked8788
theorem derived8788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8788 := by
  apply localUnsat_implies_entails f8788 [c7467, c7388, c7390, c7391, c7323, c7382, c7352, c7846] c8788 unsat8788 (by rfl) a
  have h0 : Entails.eval a c7467 := derived7467 a h
  have h1 : Entails.eval a c7388 := derived7388 a h
  have h2 : Entails.eval a c7390 := derived7390 a h
  have h3 : Entails.eval a c7391 := derived7391 a h
  have h4 : Entails.eval a c7323 := derived7323 a h
  have h5 : Entails.eval a c7382 := derived7382 a h
  have h6 : Entails.eval a c7352 := derived7352 a h
  have h7 : Entails.eval a c7846 := derived7846 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8789 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8788, some c7567, some c7375, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8789 : lratChecker f8789 p8789 = .success := by decide +kernel
theorem unsat8789 : Unsatisfiable (PosFin 65) f8789 := by
  apply lratCheckerSound f8789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8789
  · intro a ha; simp [p8789] at ha; subst a; trivial
  · exact checked8789
theorem derived8789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8789 := by
  apply localUnsat_implies_entails f8789 [c8788, c7567, c7375] c8789 unsat8789 (by rfl) a
  have h0 : Entails.eval a c8788 := derived8788 a h
  have h1 : Entails.eval a c7567 := derived7567 a h
  have h2 : Entails.eval a c7375 := derived7375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8790 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8785, some c8772, some c8761, some c8787, some c7356, some c8789, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8790 : lratChecker f8790 p8790 = .success := by decide +kernel
theorem unsat8790 : Unsatisfiable (PosFin 65) f8790 := by
  apply lratCheckerSound f8790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8790
  · intro a ha; simp [p8790] at ha; subst a; trivial
  · exact checked8790
theorem derived8790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8790 := by
  apply localUnsat_implies_entails f8790 [c8785, c8772, c8761, c8787, c7356, c8789] c8790 unsat8790 (by rfl) a
  have h0 : Entails.eval a c8785 := derived8785 a h
  have h1 : Entails.eval a c8772 := derived8772 a h
  have h2 : Entails.eval a c8761 := derived8761 a h
  have h3 : Entails.eval a c8787 := derived8787 a h
  have h4 : Entails.eval a c7356 := derived7356 a h
  have h5 : Entails.eval a c8789 := derived8789 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8791 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6669, some c6697, some c42, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8791 : lratChecker f8791 p8791 = .success := by decide +kernel
theorem unsat8791 : Unsatisfiable (PosFin 65) f8791 := by
  apply lratCheckerSound f8791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8791
  · intro a ha; simp [p8791] at ha; subst a; trivial
  · exact checked8791
theorem derived8791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8791 := by
  apply localUnsat_implies_entails f8791 [c6669, c6697, c42] c8791 unsat8791 (by rfl) a
  have h0 : Entails.eval a c6669 := derived6669 a h
  have h1 : Entails.eval a c6697 := derived6697 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8792 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c16, some c17, some c6666, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8792 : lratChecker f8792 p8792 = .success := by decide +kernel
theorem unsat8792 : Unsatisfiable (PosFin 65) f8792 := by
  apply lratCheckerSound f8792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8792
  · intro a ha; simp [p8792] at ha; subst a; trivial
  · exact checked8792
theorem derived8792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8792 := by
  apply localUnsat_implies_entails f8792 [c16, c17, c6666] c8792 unsat8792 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c6666 := derived6666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8793 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨58, by decide⟩, false), (⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8791, some c8792, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8793 : lratChecker f8793 p8793 = .success := by decide +kernel
theorem unsat8793 : Unsatisfiable (PosFin 65) f8793 := by
  apply lratCheckerSound f8793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8793
  · intro a ha; simp [p8793] at ha; subst a; trivial
  · exact checked8793
theorem derived8793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8793 := by
  apply localUnsat_implies_entails f8793 [c8791, c8792] c8793 unsat8793 (by rfl) a
  have h0 : Entails.eval a c8791 := derived8791 a h
  have h1 : Entails.eval a c8792 := derived8792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8794 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8781, some c8783, some c755, some c793, some c7439, some c1111, some c2616, some c1142, some c1830, some c7485, some c2544, some c1816, some c1143, some c2513, some c1230, some c2069, some c8793, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8794 : lratChecker f8794 p8794 = .success := by decide +kernel
theorem unsat8794 : Unsatisfiable (PosFin 65) f8794 := by
  apply lratCheckerSound f8794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8794
  · intro a ha; simp [p8794] at ha; subst a; trivial
  · exact checked8794
theorem derived8794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8794 := by
  apply localUnsat_implies_entails f8794 [c8781, c8783, c755, c793, c7439, c1111, c2616, c1142, c1830, c7485, c2544, c1816, c1143, c2513, c1230, c2069, c8793] c8794 unsat8794 (by rfl) a
  have h0 : Entails.eval a c8781 := derived8781 a h
  have h1 : Entails.eval a c8783 := derived8783 a h
  have h2 : Entails.eval a c755 := h 754 (by decide)
  have h3 : Entails.eval a c793 := h 792 (by decide)
  have h4 : Entails.eval a c7439 := derived7439 a h
  have h5 : Entails.eval a c1111 := h 1110 (by decide)
  have h6 : Entails.eval a c2616 := h 2615 (by decide)
  have h7 : Entails.eval a c1142 := h 1141 (by decide)
  have h8 : Entails.eval a c1830 := h 1829 (by decide)
  have h9 : Entails.eval a c7485 := derived7485 a h
  have h10 : Entails.eval a c2544 := h 2543 (by decide)
  have h11 : Entails.eval a c1816 := h 1815 (by decide)
  have h12 : Entails.eval a c1143 := h 1142 (by decide)
  have h13 : Entails.eval a c2513 := h 2512 (by decide)
  have h14 : Entails.eval a c1230 := h 1229 (by decide)
  have h15 : Entails.eval a c2069 := h 2068 (by decide)
  have h16 : Entails.eval a c8793 := derived8793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8795 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8670, some c8761, some c8772, some c8785, some c8790, some c8794, some c7356, some c7439, some c106, some c6747, some c6748, some c3116, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8795 : lratChecker f8795 p8795 = .success := by decide +kernel
theorem unsat8795 : Unsatisfiable (PosFin 65) f8795 := by
  apply lratCheckerSound f8795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8795
  · intro a ha; simp [p8795] at ha; subst a; trivial
  · exact checked8795
theorem derived8795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8795 := by
  apply localUnsat_implies_entails f8795 [c8670, c8761, c8772, c8785, c8790, c8794, c7356, c7439, c106, c6747, c6748, c3116] c8795 unsat8795 (by rfl) a
  have h0 : Entails.eval a c8670 := derived8670 a h
  have h1 : Entails.eval a c8761 := derived8761 a h
  have h2 : Entails.eval a c8772 := derived8772 a h
  have h3 : Entails.eval a c8785 := derived8785 a h
  have h4 : Entails.eval a c8790 := derived8790 a h
  have h5 : Entails.eval a c8794 := derived8794 a h
  have h6 : Entails.eval a c7356 := derived7356 a h
  have h7 : Entails.eval a c7439 := derived7439 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c6747 := derived6747 a h
  have h10 : Entails.eval a c6748 := derived6748 a h
  have h11 : Entails.eval a c3116 := h 3115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8796 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7316, some c7657, some c1125, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p8796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8796 : lratChecker f8796 p8796 = .success := by decide +kernel
theorem unsat8796 : Unsatisfiable (PosFin 65) f8796 := by
  apply lratCheckerSound f8796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8796
  · intro a ha; simp [p8796] at ha; subst a; trivial
  · exact checked8796
theorem derived8796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8796 := by
  apply localUnsat_implies_entails f8796 [c7316, c7657, c1125] c8796 unsat8796 (by rfl) a
  have h0 : Entails.eval a c7316 := derived7316 a h
  have h1 : Entails.eval a c7657 := derived7657 a h
  have h2 : Entails.eval a c1125 := h 1124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8797 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c7694, some c398, some c413, some c406, some c400, some c381, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8797 : lratChecker f8797 p8797 = .success := by decide +kernel
theorem unsat8797 : Unsatisfiable (PosFin 65) f8797 := by
  apply lratCheckerSound f8797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8797
  · intro a ha; simp [p8797] at ha; subst a; trivial
  · exact checked8797
theorem derived8797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8797 := by
  apply localUnsat_implies_entails f8797 [c7534, c7694, c398, c413, c406, c400, c381] c8797 unsat8797 (by rfl) a
  have h0 : Entails.eval a c7534 := derived7534 a h
  have h1 : Entails.eval a c7694 := derived7694 a h
  have h2 : Entails.eval a c398 := h 397 (by decide)
  have h3 : Entails.eval a c413 := h 412 (by decide)
  have h4 : Entails.eval a c406 := h 405 (by decide)
  have h5 : Entails.eval a c400 := h 399 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8798 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7788, some c8797, some c7657, some c8796, some c1125, some c1126, some c317, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8798 : lratChecker f8798 p8798 = .success := by decide +kernel
theorem unsat8798 : Unsatisfiable (PosFin 65) f8798 := by
  apply lratCheckerSound f8798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8798
  · intro a ha; simp [p8798] at ha; subst a; trivial
  · exact checked8798
theorem derived8798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8798 := by
  apply localUnsat_implies_entails f8798 [c7788, c8797, c7657, c8796, c1125, c1126, c317] c8798 unsat8798 (by rfl) a
  have h0 : Entails.eval a c7788 := derived7788 a h
  have h1 : Entails.eval a c8797 := derived8797 a h
  have h2 : Entails.eval a c7657 := derived7657 a h
  have h3 : Entails.eval a c8796 := derived8796 a h
  have h4 : Entails.eval a c1125 := h 1124 (by decide)
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8799 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7534, some c8714, some c8715, some c8798, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8799 : lratChecker f8799 p8799 = .success := by decide +kernel
theorem unsat8799 : Unsatisfiable (PosFin 65) f8799 := by
  apply lratCheckerSound f8799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8799
  · intro a ha; simp [p8799] at ha; subst a; trivial
  · exact checked8799
theorem derived8799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8799 := by
  apply localUnsat_implies_entails f8799 [c7534, c8714, c8715, c8798] c8799 unsat8799 (by rfl) a
  have h0 : Entails.eval a c7534 := derived7534 a h
  have h1 : Entails.eval a c8714 := derived8714 a h
  have h2 : Entails.eval a c8715 := derived8715 a h
  have h3 : Entails.eval a c8798 := derived8798 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8800 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8799, some c7565, some c7791, some c7689, some c7646, some c7771, some c7657, some c311, some c1761, some c7768, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8800 : lratChecker f8800 p8800 = .success := by decide +kernel
theorem unsat8800 : Unsatisfiable (PosFin 65) f8800 := by
  apply lratCheckerSound f8800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8800
  · intro a ha; simp [p8800] at ha; subst a; trivial
  · exact checked8800
theorem derived8800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8800 := by
  apply localUnsat_implies_entails f8800 [c8799, c7565, c7791, c7689, c7646, c7771, c7657, c311, c1761, c7768] c8800 unsat8800 (by rfl) a
  have h0 : Entails.eval a c8799 := derived8799 a h
  have h1 : Entails.eval a c7565 := derived7565 a h
  have h2 : Entails.eval a c7791 := derived7791 a h
  have h3 : Entails.eval a c7689 := derived7689 a h
  have h4 : Entails.eval a c7646 := derived7646 a h
  have h5 : Entails.eval a c7771 := derived7771 a h
  have h6 : Entails.eval a c7657 := derived7657 a h
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c1761 := h 1760 (by decide)
  have h9 : Entails.eval a c7768 := derived7768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8801 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8799, some c8800, some c8725, some c191, some c1808, some c407, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p8801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8801 : lratChecker f8801 p8801 = .success := by decide +kernel
theorem unsat8801 : Unsatisfiable (PosFin 65) f8801 := by
  apply lratCheckerSound f8801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8801
  · intro a ha; simp [p8801] at ha; subst a; trivial
  · exact checked8801
theorem derived8801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8801 := by
  apply localUnsat_implies_entails f8801 [c8799, c8800, c8725, c191, c1808, c407] c8801 unsat8801 (by rfl) a
  have h0 : Entails.eval a c8799 := derived8799 a h
  have h1 : Entails.eval a c8800 := derived8800 a h
  have h2 : Entails.eval a c8725 := derived8725 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c1808 := h 1807 (by decide)
  have h5 : Entails.eval a c407 := h 406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8802 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8801, some c7534, some c8764, some c7663, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8802 : lratChecker f8802 p8802 = .success := by decide +kernel
theorem unsat8802 : Unsatisfiable (PosFin 65) f8802 := by
  apply lratCheckerSound f8802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8802
  · intro a ha; simp [p8802] at ha; subst a; trivial
  · exact checked8802
theorem derived8802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8802 := by
  apply localUnsat_implies_entails f8802 [c8801, c7534, c8764, c7663] c8802 unsat8802 (by rfl) a
  have h0 : Entails.eval a c8801 := derived8801 a h
  have h1 : Entails.eval a c7534 := derived7534 a h
  have h2 : Entails.eval a c8764 := derived8764 a h
  have h3 : Entails.eval a c7663 := derived7663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8803 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8802, some c8801, some c7565, some c7826, some c7791, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8803 : lratChecker f8803 p8803 = .success := by decide +kernel
theorem unsat8803 : Unsatisfiable (PosFin 65) f8803 := by
  apply lratCheckerSound f8803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8803
  · intro a ha; simp [p8803] at ha; subst a; trivial
  · exact checked8803
theorem derived8803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8803 := by
  apply localUnsat_implies_entails f8803 [c8802, c8801, c7565, c7826, c7791] c8803 unsat8803 (by rfl) a
  have h0 : Entails.eval a c8802 := derived8802 a h
  have h1 : Entails.eval a c8801 := derived8801 a h
  have h2 : Entails.eval a c7565 := derived7565 a h
  have h3 : Entails.eval a c7826 := derived7826 a h
  have h4 : Entails.eval a c7791 := derived7791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8804 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8803, some c8802, some c7139, some c8801, some c7467, some c392, some c1797, some c7323, some c1761, some c226, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8804 : lratChecker f8804 p8804 = .success := by decide +kernel
theorem unsat8804 : Unsatisfiable (PosFin 65) f8804 := by
  apply lratCheckerSound f8804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8804
  · intro a ha; simp [p8804] at ha; subst a; trivial
  · exact checked8804
theorem derived8804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8804 := by
  apply localUnsat_implies_entails f8804 [c8803, c8802, c7139, c8801, c7467, c392, c1797, c7323, c1761, c226] c8804 unsat8804 (by rfl) a
  have h0 : Entails.eval a c8803 := derived8803 a h
  have h1 : Entails.eval a c8802 := derived8802 a h
  have h2 : Entails.eval a c7139 := derived7139 a h
  have h3 : Entails.eval a c8801 := derived8801 a h
  have h4 : Entails.eval a c7467 := derived7467 a h
  have h5 : Entails.eval a c392 := h 391 (by decide)
  have h6 : Entails.eval a c1797 := h 1796 (by decide)
  have h7 : Entails.eval a c7323 := derived7323 a h
  have h8 : Entails.eval a c1761 := h 1760 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8805 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8803, some c8801, some c7467, some c8802, some c7139, some c8804, some c397, some c229, some c1797, some c1761, some c1769, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8805 : lratChecker f8805 p8805 = .success := by decide +kernel
theorem unsat8805 : Unsatisfiable (PosFin 65) f8805 := by
  apply lratCheckerSound f8805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8805
  · intro a ha; simp [p8805] at ha; subst a; trivial
  · exact checked8805
theorem derived8805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8805 := by
  apply localUnsat_implies_entails f8805 [c8803, c8801, c7467, c8802, c7139, c8804, c397, c229, c1797, c1761, c1769] c8805 unsat8805 (by rfl) a
  have h0 : Entails.eval a c8803 := derived8803 a h
  have h1 : Entails.eval a c8801 := derived8801 a h
  have h2 : Entails.eval a c7467 := derived7467 a h
  have h3 : Entails.eval a c8802 := derived8802 a h
  have h4 : Entails.eval a c7139 := derived7139 a h
  have h5 : Entails.eval a c8804 := derived8804 a h
  have h6 : Entails.eval a c397 := h 396 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c1797 := h 1796 (by decide)
  have h9 : Entails.eval a c1761 := h 1760 (by decide)
  have h10 : Entails.eval a c1769 := h 1768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8806 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8803, some c8801, some c7467, some c8805, some c8802, some c7254, some c7251, some c1804, some c1797, some c1620, some c7219, some c1717, some c1582, some c7323, some c1794, some c1803, some c7352, some c1604, some c1755, some c2629, some c2135, some c1398, some c7213, some c1730, some c1731, some c6665, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked8806 : lratChecker f8806 p8806 = .success := by decide +kernel
theorem unsat8806 : Unsatisfiable (PosFin 65) f8806 := by
  apply lratCheckerSound f8806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8806
  · intro a ha; simp [p8806] at ha; subst a; trivial
  · exact checked8806
theorem derived8806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8806 := by
  apply localUnsat_implies_entails f8806 [c8803, c8801, c7467, c8805, c8802, c7254, c7251, c1804, c1797, c1620, c7219, c1717, c1582, c7323, c1794, c1803, c7352, c1604, c1755, c2629, c2135, c1398, c7213, c1730, c1731, c6665] c8806 unsat8806 (by rfl) a
  have h0 : Entails.eval a c8803 := derived8803 a h
  have h1 : Entails.eval a c8801 := derived8801 a h
  have h2 : Entails.eval a c7467 := derived7467 a h
  have h3 : Entails.eval a c8805 := derived8805 a h
  have h4 : Entails.eval a c8802 := derived8802 a h
  have h5 : Entails.eval a c7254 := derived7254 a h
  have h6 : Entails.eval a c7251 := derived7251 a h
  have h7 : Entails.eval a c1804 := h 1803 (by decide)
  have h8 : Entails.eval a c1797 := h 1796 (by decide)
  have h9 : Entails.eval a c1620 := h 1619 (by decide)
  have h10 : Entails.eval a c7219 := derived7219 a h
  have h11 : Entails.eval a c1717 := h 1716 (by decide)
  have h12 : Entails.eval a c1582 := h 1581 (by decide)
  have h13 : Entails.eval a c7323 := derived7323 a h
  have h14 : Entails.eval a c1794 := h 1793 (by decide)
  have h15 : Entails.eval a c1803 := h 1802 (by decide)
  have h16 : Entails.eval a c7352 := derived7352 a h
  have h17 : Entails.eval a c1604 := h 1603 (by decide)
  have h18 : Entails.eval a c1755 := h 1754 (by decide)
  have h19 : Entails.eval a c2629 := h 2628 (by decide)
  have h20 : Entails.eval a c2135 := h 2134 (by decide)
  have h21 : Entails.eval a c1398 := h 1397 (by decide)
  have h22 : Entails.eval a c7213 := derived7213 a h
  have h23 : Entails.eval a c1730 := h 1729 (by decide)
  have h24 : Entails.eval a c1731 := h 1730 (by decide)
  have h25 : Entails.eval a c6665 := derived6665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8807 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8801, some c8802, some c8805, some c7251, some c8803, some c7467, some c7254, some c1797, some c1794, some c1804, some c1620, some c7323, some c7219, some c1803, some c1717, some c7352, some c1604, some c1582, some c1755, some c8806, some c2136, some c2626, some c1399, some c7211, some c1730, some c1731, some c6665, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked8807 : lratChecker f8807 p8807 = .success := by decide +kernel
theorem unsat8807 : Unsatisfiable (PosFin 65) f8807 := by
  apply lratCheckerSound f8807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8807
  · intro a ha; simp [p8807] at ha; subst a; trivial
  · exact checked8807
theorem derived8807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8807 := by
  apply localUnsat_implies_entails f8807 [c8801, c8802, c8805, c7251, c8803, c7467, c7254, c1797, c1794, c1804, c1620, c7323, c7219, c1803, c1717, c7352, c1604, c1582, c1755, c8806, c2136, c2626, c1399, c7211, c1730, c1731, c6665] c8807 unsat8807 (by rfl) a
  have h0 : Entails.eval a c8801 := derived8801 a h
  have h1 : Entails.eval a c8802 := derived8802 a h
  have h2 : Entails.eval a c8805 := derived8805 a h
  have h3 : Entails.eval a c7251 := derived7251 a h
  have h4 : Entails.eval a c8803 := derived8803 a h
  have h5 : Entails.eval a c7467 := derived7467 a h
  have h6 : Entails.eval a c7254 := derived7254 a h
  have h7 : Entails.eval a c1797 := h 1796 (by decide)
  have h8 : Entails.eval a c1794 := h 1793 (by decide)
  have h9 : Entails.eval a c1804 := h 1803 (by decide)
  have h10 : Entails.eval a c1620 := h 1619 (by decide)
  have h11 : Entails.eval a c7323 := derived7323 a h
  have h12 : Entails.eval a c7219 := derived7219 a h
  have h13 : Entails.eval a c1803 := h 1802 (by decide)
  have h14 : Entails.eval a c1717 := h 1716 (by decide)
  have h15 : Entails.eval a c7352 := derived7352 a h
  have h16 : Entails.eval a c1604 := h 1603 (by decide)
  have h17 : Entails.eval a c1582 := h 1581 (by decide)
  have h18 : Entails.eval a c1755 := h 1754 (by decide)
  have h19 : Entails.eval a c8806 := derived8806 a h
  have h20 : Entails.eval a c2136 := h 2135 (by decide)
  have h21 : Entails.eval a c2626 := h 2625 (by decide)
  have h22 : Entails.eval a c1399 := h 1398 (by decide)
  have h23 : Entails.eval a c7211 := derived7211 a h
  have h24 : Entails.eval a c1730 := h 1729 (by decide)
  have h25 : Entails.eval a c1731 := h 1730 (by decide)
  have h26 : Entails.eval a c6665 := derived6665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8808 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false), (⟨26, by decide⟩, true), (⟨59, by decide⟩, true), (⟨27, by decide⟩, true), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8801, some c318, some c8803, some c8802, some c175, some c7352, some c7251, some c7168, some c2629, some c2135, some c2093, some c2602, some c7190, some c1829, some c32, some c1272, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8808 : lratChecker f8808 p8808 = .success := by decide +kernel
theorem unsat8808 : Unsatisfiable (PosFin 65) f8808 := by
  apply lratCheckerSound f8808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8808
  · intro a ha; simp [p8808] at ha; subst a; trivial
  · exact checked8808
theorem derived8808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8808 := by
  apply localUnsat_implies_entails f8808 [c8801, c318, c8803, c8802, c175, c7352, c7251, c7168, c2629, c2135, c2093, c2602, c7190, c1829, c32, c1272] c8808 unsat8808 (by rfl) a
  have h0 : Entails.eval a c8801 := derived8801 a h
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c8803 := derived8803 a h
  have h3 : Entails.eval a c8802 := derived8802 a h
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c7352 := derived7352 a h
  have h6 : Entails.eval a c7251 := derived7251 a h
  have h7 : Entails.eval a c7168 := derived7168 a h
  have h8 : Entails.eval a c2629 := h 2628 (by decide)
  have h9 : Entails.eval a c2135 := h 2134 (by decide)
  have h10 : Entails.eval a c2093 := h 2092 (by decide)
  have h11 : Entails.eval a c2602 := h 2601 (by decide)
  have h12 : Entails.eval a c7190 := derived7190 a h
  have h13 : Entails.eval a c1829 := h 1828 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c1272 := h 1271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8809 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8795, some c8742, some c8803, some c8802, some c8801, some c8670, some c7467, some c8805, some c7251, some c8807, some c7138, some c175, some c299, some c7726, some c306, some c180, some c305, some c7354, some c304, some c7352, some c318, some c8808, some c2626, some c7248, some c2598, some c1834, some c2136, some c8792, some c7211, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked8809 : lratChecker f8809 p8809 = .success := by decide +kernel
theorem unsat8809 : Unsatisfiable (PosFin 65) f8809 := by
  apply lratCheckerSound f8809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8809
  · intro a ha; simp [p8809] at ha; subst a; trivial
  · exact checked8809
theorem derived8809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8809 := by
  apply localUnsat_implies_entails f8809 [c8795, c8742, c8803, c8802, c8801, c8670, c7467, c8805, c7251, c8807, c7138, c175, c299, c7726, c306, c180, c305, c7354, c304, c7352, c318, c8808, c2626, c7248, c2598, c1834, c2136, c8792, c7211] c8809 unsat8809 (by rfl) a
  have h0 : Entails.eval a c8795 := derived8795 a h
  have h1 : Entails.eval a c8742 := derived8742 a h
  have h2 : Entails.eval a c8803 := derived8803 a h
  have h3 : Entails.eval a c8802 := derived8802 a h
  have h4 : Entails.eval a c8801 := derived8801 a h
  have h5 : Entails.eval a c8670 := derived8670 a h
  have h6 : Entails.eval a c7467 := derived7467 a h
  have h7 : Entails.eval a c8805 := derived8805 a h
  have h8 : Entails.eval a c7251 := derived7251 a h
  have h9 : Entails.eval a c8807 := derived8807 a h
  have h10 : Entails.eval a c7138 := derived7138 a h
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c7726 := derived7726 a h
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c7354 := derived7354 a h
  have h18 : Entails.eval a c304 := h 303 (by decide)
  have h19 : Entails.eval a c7352 := derived7352 a h
  have h20 : Entails.eval a c318 := h 317 (by decide)
  have h21 : Entails.eval a c8808 := derived8808 a h
  have h22 : Entails.eval a c2626 := h 2625 (by decide)
  have h23 : Entails.eval a c7248 := derived7248 a h
  have h24 : Entails.eval a c2598 := h 2597 (by decide)
  have h25 : Entails.eval a c1834 := h 1833 (by decide)
  have h26 : Entails.eval a c2136 := h 2135 (by decide)
  have h27 : Entails.eval a c8792 := derived8792 a h
  have h28 : Entails.eval a c7211 := derived7211 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8810 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8795, some c8742, some c8802, some c8803, some c8809, some c308, some c273, some c1624, some c7243, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8810 : lratChecker f8810 p8810 = .success := by decide +kernel
theorem unsat8810 : Unsatisfiable (PosFin 65) f8810 := by
  apply lratCheckerSound f8810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8810
  · intro a ha; simp [p8810] at ha; subst a; trivial
  · exact checked8810
theorem derived8810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8810 := by
  apply localUnsat_implies_entails f8810 [c8795, c8742, c8802, c8803, c8809, c308, c273, c1624, c7243] c8810 unsat8810 (by rfl) a
  have h0 : Entails.eval a c8795 := derived8795 a h
  have h1 : Entails.eval a c8742 := derived8742 a h
  have h2 : Entails.eval a c8802 := derived8802 a h
  have h3 : Entails.eval a c8803 := derived8803 a h
  have h4 : Entails.eval a c8809 := derived8809 a h
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c1624 := h 1623 (by decide)
  have h8 : Entails.eval a c7243 := derived7243 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8811 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8810, some c8752, some c8795, some c8718, some c7668, some c7616, some c7680, some c7697, some c7683, some c7684, some c1010, some c1155, some c2335, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8811 : lratChecker f8811 p8811 = .success := by decide +kernel
theorem unsat8811 : Unsatisfiable (PosFin 65) f8811 := by
  apply lratCheckerSound f8811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8811
  · intro a ha; simp [p8811] at ha; subst a; trivial
  · exact checked8811
theorem derived8811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8811 := by
  apply localUnsat_implies_entails f8811 [c8810, c8752, c8795, c8718, c7668, c7616, c7680, c7697, c7683, c7684, c1010, c1155, c2335] c8811 unsat8811 (by rfl) a
  have h0 : Entails.eval a c8810 := derived8810 a h
  have h1 : Entails.eval a c8752 := derived8752 a h
  have h2 : Entails.eval a c8795 := derived8795 a h
  have h3 : Entails.eval a c8718 := derived8718 a h
  have h4 : Entails.eval a c7668 := derived7668 a h
  have h5 : Entails.eval a c7616 := derived7616 a h
  have h6 : Entails.eval a c7680 := derived7680 a h
  have h7 : Entails.eval a c7697 := derived7697 a h
  have h8 : Entails.eval a c7683 := derived7683 a h
  have h9 : Entails.eval a c7684 := derived7684 a h
  have h10 : Entails.eval a c1010 := h 1009 (by decide)
  have h11 : Entails.eval a c1155 := h 1154 (by decide)
  have h12 : Entails.eval a c2335 := h 2334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8812 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8810, some c8795, some c8752, some c8811, some c7430, some c7549, some c7595, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8812 : lratChecker f8812 p8812 = .success := by decide +kernel
theorem unsat8812 : Unsatisfiable (PosFin 65) f8812 := by
  apply lratCheckerSound f8812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8812
  · intro a ha; simp [p8812] at ha; subst a; trivial
  · exact checked8812
theorem derived8812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8812 := by
  apply localUnsat_implies_entails f8812 [c8810, c8795, c8752, c8811, c7430, c7549, c7595] c8812 unsat8812 (by rfl) a
  have h0 : Entails.eval a c8810 := derived8810 a h
  have h1 : Entails.eval a c8795 := derived8795 a h
  have h2 : Entails.eval a c8752 := derived8752 a h
  have h3 : Entails.eval a c8811 := derived8811 a h
  have h4 : Entails.eval a c7430 := derived7430 a h
  have h5 : Entails.eval a c7549 := derived7549 a h
  have h6 : Entails.eval a c7595 := derived7595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8813 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7843, some c7825, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8813 : lratChecker f8813 p8813 = .success := by decide +kernel
theorem unsat8813 : Unsatisfiable (PosFin 65) f8813 := by
  apply lratCheckerSound f8813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8813
  · intro a ha; simp [p8813] at ha; subst a; trivial
  · exact checked8813
theorem derived8813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8813 := by
  apply localUnsat_implies_entails f8813 [c7843, c7825] c8813 unsat8813 (by rfl) a
  have h0 : Entails.eval a c7843 := derived7843 a h
  have h1 : Entails.eval a c7825 := derived7825 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8814 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7708, some c8813, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8814 : lratChecker f8814 p8814 = .success := by decide +kernel
theorem unsat8814 : Unsatisfiable (PosFin 65) f8814 := by
  apply lratCheckerSound f8814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8814
  · intro a ha; simp [p8814] at ha; subst a; trivial
  · exact checked8814
theorem derived8814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8814 := by
  apply localUnsat_implies_entails f8814 [c7708, c8813] c8814 unsat8814 (by rfl) a
  have h0 : Entails.eval a c7708 := derived7708 a h
  have h1 : Entails.eval a c8813 := derived8813 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8815 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7466, some c8814, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8815 : lratChecker f8815 p8815 = .success := by decide +kernel
theorem unsat8815 : Unsatisfiable (PosFin 65) f8815 := by
  apply lratCheckerSound f8815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8815
  · intro a ha; simp [p8815] at ha; subst a; trivial
  · exact checked8815
theorem derived8815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8815 := by
  apply localUnsat_implies_entails f8815 [c7466, c8814] c8815 unsat8815 (by rfl) a
  have h0 : Entails.eval a c7466 := derived7466 a h
  have h1 : Entails.eval a c8814 := derived8814 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8816 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8815, some c8779, some c7549, some c7599, some c7680, some c7697, some c7610, some c7683, some c7707, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8816 : lratChecker f8816 p8816 = .success := by decide +kernel
theorem unsat8816 : Unsatisfiable (PosFin 65) f8816 := by
  apply lratCheckerSound f8816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8816
  · intro a ha; simp [p8816] at ha; subst a; trivial
  · exact checked8816
theorem derived8816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8816 := by
  apply localUnsat_implies_entails f8816 [c8815, c8779, c7549, c7599, c7680, c7697, c7610, c7683, c7707] c8816 unsat8816 (by rfl) a
  have h0 : Entails.eval a c8815 := derived8815 a h
  have h1 : Entails.eval a c8779 := derived8779 a h
  have h2 : Entails.eval a c7549 := derived7549 a h
  have h3 : Entails.eval a c7599 := derived7599 a h
  have h4 : Entails.eval a c7680 := derived7680 a h
  have h5 : Entails.eval a c7697 := derived7697 a h
  have h6 : Entails.eval a c7610 := derived7610 a h
  have h7 : Entails.eval a c7683 := derived7683 a h
  have h8 : Entails.eval a c7707 := derived7707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8817 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8816, some c8815, some c8779, some c748, some c7944, some c781, some c272, some c771, some c258, some c270, some c246, some c6667, some c8619, some c6760, some c3377, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8817 : lratChecker f8817 p8817 = .success := by decide +kernel
theorem unsat8817 : Unsatisfiable (PosFin 65) f8817 := by
  apply lratCheckerSound f8817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8817
  · intro a ha; simp [p8817] at ha; subst a; trivial
  · exact checked8817
theorem derived8817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8817 := by
  apply localUnsat_implies_entails f8817 [c8816, c8815, c8779, c748, c7944, c781, c272, c771, c258, c270, c246, c6667, c8619, c6760, c3377] c8817 unsat8817 (by rfl) a
  have h0 : Entails.eval a c8816 := derived8816 a h
  have h1 : Entails.eval a c8815 := derived8815 a h
  have h2 : Entails.eval a c8779 := derived8779 a h
  have h3 : Entails.eval a c748 := h 747 (by decide)
  have h4 : Entails.eval a c7944 := derived7944 a h
  have h5 : Entails.eval a c781 := h 780 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c771 := h 770 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c6667 := derived6667 a h
  have h12 : Entails.eval a c8619 := derived8619 a h
  have h13 : Entails.eval a c6760 := derived6760 a h
  have h14 : Entails.eval a c3377 := h 3376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8818 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7445, some c1772, some c1447, some c1429, some c1409, some c8619, some c6760, some c1753, some c1408, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8818 : lratChecker f8818 p8818 = .success := by decide +kernel
theorem unsat8818 : Unsatisfiable (PosFin 65) f8818 := by
  apply lratCheckerSound f8818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8818
  · intro a ha; simp [p8818] at ha; subst a; trivial
  · exact checked8818
theorem derived8818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8818 := by
  apply localUnsat_implies_entails f8818 [c7445, c1772, c1447, c1429, c1409, c8619, c6760, c1753, c1408] c8818 unsat8818 (by rfl) a
  have h0 : Entails.eval a c7445 := derived7445 a h
  have h1 : Entails.eval a c1772 := h 1771 (by decide)
  have h2 : Entails.eval a c1447 := h 1446 (by decide)
  have h3 : Entails.eval a c1429 := h 1428 (by decide)
  have h4 : Entails.eval a c1409 := h 1408 (by decide)
  have h5 : Entails.eval a c8619 := derived8619 a h
  have h6 : Entails.eval a c6760 := derived6760 a h
  have h7 : Entails.eval a c1753 := h 1752 (by decide)
  have h8 : Entails.eval a c1408 := h 1407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8819 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8810, some c8795, some c8670, some c8812, some c8815, some c8779, some c8816, some c7394, some c7444, some c8817, some c1419, some c8818, some c108, some c1296, some c7596, some c7946, some c1432, some c6710, some c8728, some c1321, some c1628, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8819 : lratChecker f8819 p8819 = .success := by decide +kernel
theorem unsat8819 : Unsatisfiable (PosFin 65) f8819 := by
  apply lratCheckerSound f8819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8819
  · intro a ha; simp [p8819] at ha; subst a; trivial
  · exact checked8819
theorem derived8819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8819 := by
  apply localUnsat_implies_entails f8819 [c8810, c8795, c8670, c8812, c8815, c8779, c8816, c7394, c7444, c8817, c1419, c8818, c108, c1296, c7596, c7946, c1432, c6710, c8728, c1321, c1628] c8819 unsat8819 (by rfl) a
  have h0 : Entails.eval a c8810 := derived8810 a h
  have h1 : Entails.eval a c8795 := derived8795 a h
  have h2 : Entails.eval a c8670 := derived8670 a h
  have h3 : Entails.eval a c8812 := derived8812 a h
  have h4 : Entails.eval a c8815 := derived8815 a h
  have h5 : Entails.eval a c8779 := derived8779 a h
  have h6 : Entails.eval a c8816 := derived8816 a h
  have h7 : Entails.eval a c7394 := derived7394 a h
  have h8 : Entails.eval a c7444 := derived7444 a h
  have h9 : Entails.eval a c8817 := derived8817 a h
  have h10 : Entails.eval a c1419 := h 1418 (by decide)
  have h11 : Entails.eval a c8818 := derived8818 a h
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c1296 := h 1295 (by decide)
  have h14 : Entails.eval a c7596 := derived7596 a h
  have h15 : Entails.eval a c7946 := derived7946 a h
  have h16 : Entails.eval a c1432 := h 1431 (by decide)
  have h17 : Entails.eval a c6710 := derived6710 a h
  have h18 : Entails.eval a c8728 := derived8728 a h
  have h19 : Entails.eval a c1321 := h 1320 (by decide)
  have h20 : Entails.eval a c1628 := h 1627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8820 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7795, some c7802, some c7813, some c7805, some c1125, some c1126, some c1134, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8820 : lratChecker f8820 p8820 = .success := by decide +kernel
theorem unsat8820 : Unsatisfiable (PosFin 65) f8820 := by
  apply lratCheckerSound f8820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8820
  · intro a ha; simp [p8820] at ha; subst a; trivial
  · exact checked8820
theorem derived8820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8820 := by
  apply localUnsat_implies_entails f8820 [c7795, c7802, c7813, c7805, c1125, c1126, c1134] c8820 unsat8820 (by rfl) a
  have h0 : Entails.eval a c7795 := derived7795 a h
  have h1 : Entails.eval a c7802 := derived7802 a h
  have h2 : Entails.eval a c7813 := derived7813 a h
  have h3 : Entails.eval a c7805 := derived7805 a h
  have h4 : Entails.eval a c1125 := h 1124 (by decide)
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8821 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8820, some c7668, some c7699, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p8821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8821 : lratChecker f8821 p8821 = .success := by decide +kernel
theorem unsat8821 : Unsatisfiable (PosFin 65) f8821 := by
  apply lratCheckerSound f8821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8821
  · intro a ha; simp [p8821] at ha; subst a; trivial
  · exact checked8821
theorem derived8821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8821 := by
  apply localUnsat_implies_entails f8821 [c8820, c7668, c7699] c8821 unsat8821 (by rfl) a
  have h0 : Entails.eval a c8820 := derived8820 a h
  have h1 : Entails.eval a c7668 := derived7668 a h
  have h2 : Entails.eval a c7699 := derived7699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8822 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8819, some c8810, some c8795, some c8718, some c8821, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8822 : lratChecker f8822 p8822 = .success := by decide +kernel
theorem unsat8822 : Unsatisfiable (PosFin 65) f8822 := by
  apply lratCheckerSound f8822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8822
  · intro a ha; simp [p8822] at ha; subst a; trivial
  · exact checked8822
theorem derived8822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8822 := by
  apply localUnsat_implies_entails f8822 [c8819, c8810, c8795, c8718, c8821] c8822 unsat8822 (by rfl) a
  have h0 : Entails.eval a c8819 := derived8819 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c8795 := derived8795 a h
  have h3 : Entails.eval a c8718 := derived8718 a h
  have h4 : Entails.eval a c8821 := derived8821 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8823 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8819, some c8810, some c8795, some c8822, some c7430, some c8779, some c7549, some c7592, some c7622, some c7612, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8823 : lratChecker f8823 p8823 = .success := by decide +kernel
theorem unsat8823 : Unsatisfiable (PosFin 65) f8823 := by
  apply lratCheckerSound f8823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8823
  · intro a ha; simp [p8823] at ha; subst a; trivial
  · exact checked8823
theorem derived8823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8823 := by
  apply localUnsat_implies_entails f8823 [c8819, c8810, c8795, c8822, c7430, c8779, c7549, c7592, c7622, c7612] c8823 unsat8823 (by rfl) a
  have h0 : Entails.eval a c8819 := derived8819 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c8795 := derived8795 a h
  have h3 : Entails.eval a c8822 := derived8822 a h
  have h4 : Entails.eval a c7430 := derived7430 a h
  have h5 : Entails.eval a c8779 := derived8779 a h
  have h6 : Entails.eval a c7549 := derived7549 a h
  have h7 : Entails.eval a c7592 := derived7592 a h
  have h8 : Entails.eval a c7622 := derived7622 a h
  have h9 : Entails.eval a c7612 := derived7612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8824 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8823, some c8819, some c8810, some c8795, some c7836, some c7697, some c7637, some c7639, some c7698, some c8620, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8824 : lratChecker f8824 p8824 = .success := by decide +kernel
theorem unsat8824 : Unsatisfiable (PosFin 65) f8824 := by
  apply lratCheckerSound f8824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8824
  · intro a ha; simp [p8824] at ha; subst a; trivial
  · exact checked8824
theorem derived8824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8824 := by
  apply localUnsat_implies_entails f8824 [c8823, c8819, c8810, c8795, c7836, c7697, c7637, c7639, c7698, c8620] c8824 unsat8824 (by rfl) a
  have h0 : Entails.eval a c8823 := derived8823 a h
  have h1 : Entails.eval a c8819 := derived8819 a h
  have h2 : Entails.eval a c8810 := derived8810 a h
  have h3 : Entails.eval a c8795 := derived8795 a h
  have h4 : Entails.eval a c7836 := derived7836 a h
  have h5 : Entails.eval a c7697 := derived7697 a h
  have h6 : Entails.eval a c7637 := derived7637 a h
  have h7 : Entails.eval a c7639 := derived7639 a h
  have h8 : Entails.eval a c7698 := derived7698 a h
  have h9 : Entails.eval a c8620 := derived8620 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8825 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8823, some c8819, some c8795, some c7835, some c8824, some c7668, some c7848, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8825 : lratChecker f8825 p8825 = .success := by decide +kernel
theorem unsat8825 : Unsatisfiable (PosFin 65) f8825 := by
  apply lratCheckerSound f8825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8825
  · intro a ha; simp [p8825] at ha; subst a; trivial
  · exact checked8825
theorem derived8825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8825 := by
  apply localUnsat_implies_entails f8825 [c8823, c8819, c8795, c7835, c8824, c7668, c7848] c8825 unsat8825 (by rfl) a
  have h0 : Entails.eval a c8823 := derived8823 a h
  have h1 : Entails.eval a c8819 := derived8819 a h
  have h2 : Entails.eval a c8795 := derived8795 a h
  have h3 : Entails.eval a c7835 := derived7835 a h
  have h4 : Entails.eval a c8824 := derived8824 a h
  have h5 : Entails.eval a c7668 := derived7668 a h
  have h6 : Entails.eval a c7848 := derived7848 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8826 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8823, some c8810, some c8825, some c7394, some c7467, some c7469, some c7382, some c1434, some c1438, some c7445, some c1764, some c1450, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8826 : lratChecker f8826 p8826 = .success := by decide +kernel
theorem unsat8826 : Unsatisfiable (PosFin 65) f8826 := by
  apply lratCheckerSound f8826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8826
  · intro a ha; simp [p8826] at ha; subst a; trivial
  · exact checked8826
theorem derived8826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8826 := by
  apply localUnsat_implies_entails f8826 [c8823, c8810, c8825, c7394, c7467, c7469, c7382, c1434, c1438, c7445, c1764, c1450] c8826 unsat8826 (by rfl) a
  have h0 : Entails.eval a c8823 := derived8823 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c8825 := derived8825 a h
  have h3 : Entails.eval a c7394 := derived7394 a h
  have h4 : Entails.eval a c7467 := derived7467 a h
  have h5 : Entails.eval a c7469 := derived7469 a h
  have h6 : Entails.eval a c7382 := derived7382 a h
  have h7 : Entails.eval a c1434 := h 1433 (by decide)
  have h8 : Entails.eval a c1438 := h 1437 (by decide)
  have h9 : Entails.eval a c7445 := derived7445 a h
  have h10 : Entails.eval a c1764 := h 1763 (by decide)
  have h11 : Entails.eval a c1450 := h 1449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8827 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8779, some c7549, some c7599, some c7612, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8827 : lratChecker f8827 p8827 = .success := by decide +kernel
theorem unsat8827 : Unsatisfiable (PosFin 65) f8827 := by
  apply lratCheckerSound f8827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8827
  · intro a ha; simp [p8827] at ha; subst a; trivial
  · exact checked8827
theorem derived8827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8827 := by
  apply localUnsat_implies_entails f8827 [c8779, c7549, c7599, c7612] c8827 unsat8827 (by rfl) a
  have h0 : Entails.eval a c8779 := derived8779 a h
  have h1 : Entails.eval a c7549 := derived7549 a h
  have h2 : Entails.eval a c7599 := derived7599 a h
  have h3 : Entails.eval a c7612 := derived7612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8828 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7394, some c282, some c272, some c266, some c7316, some c7440, some c787, some c258, some c270, some c246, some c280, some c6668, some c8619, some c6760, some c3377, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8828 : lratChecker f8828 p8828 = .success := by decide +kernel
theorem unsat8828 : Unsatisfiable (PosFin 65) f8828 := by
  apply lratCheckerSound f8828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8828
  · intro a ha; simp [p8828] at ha; subst a; trivial
  · exact checked8828
theorem derived8828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8828 := by
  apply localUnsat_implies_entails f8828 [c7394, c282, c272, c266, c7316, c7440, c787, c258, c270, c246, c280, c6668, c8619, c6760, c3377] c8828 unsat8828 (by rfl) a
  have h0 : Entails.eval a c7394 := derived7394 a h
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c7316 := derived7316 a h
  have h5 : Entails.eval a c7440 := derived7440 a h
  have h6 : Entails.eval a c787 := h 786 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c6668 := derived6668 a h
  have h12 : Entails.eval a c8619 := derived8619 a h
  have h13 : Entails.eval a c6760 := derived6760 a h
  have h14 : Entails.eval a c3377 := h 3376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8829 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1811, some c7316, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p8829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8829 : lratChecker f8829 p8829 = .success := by decide +kernel
theorem unsat8829 : Unsatisfiable (PosFin 65) f8829 := by
  apply lratCheckerSound f8829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8829
  · intro a ha; simp [p8829] at ha; subst a; trivial
  · exact checked8829
theorem derived8829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8829 := by
  apply localUnsat_implies_entails f8829 [c1811, c7316] c8829 unsat8829 (by rfl) a
  have h0 : Entails.eval a c1811 := h 1810 (by decide)
  have h1 : Entails.eval a c7316 := derived7316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8830 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1367, some c1296, some c7946, some c1051, some c7682, some c2533, some c2031, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p8830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8830 : lratChecker f8830 p8830 = .success := by decide +kernel
theorem unsat8830 : Unsatisfiable (PosFin 65) f8830 := by
  apply lratCheckerSound f8830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8830
  · intro a ha; simp [p8830] at ha; subst a; trivial
  · exact checked8830
theorem derived8830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8830 := by
  apply localUnsat_implies_entails f8830 [c1367, c1296, c7946, c1051, c7682, c2533, c2031] c8830 unsat8830 (by rfl) a
  have h0 : Entails.eval a c1367 := h 1366 (by decide)
  have h1 : Entails.eval a c1296 := h 1295 (by decide)
  have h2 : Entails.eval a c7946 := derived7946 a h
  have h3 : Entails.eval a c1051 := h 1050 (by decide)
  have h4 : Entails.eval a c7682 := derived7682 a h
  have h5 : Entails.eval a c2533 := h 2532 (by decide)
  have h6 : Entails.eval a c2031 := h 2030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8831 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8827, some c7394, some c8829, some c8779, some c8828, some c8830, some c7454, some c8818, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8831 : lratChecker f8831 p8831 = .success := by decide +kernel
theorem unsat8831 : Unsatisfiable (PosFin 65) f8831 := by
  apply lratCheckerSound f8831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8831
  · intro a ha; simp [p8831] at ha; subst a; trivial
  · exact checked8831
theorem derived8831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8831 := by
  apply localUnsat_implies_entails f8831 [c8827, c7394, c8829, c8779, c8828, c8830, c7454, c8818] c8831 unsat8831 (by rfl) a
  have h0 : Entails.eval a c8827 := derived8827 a h
  have h1 : Entails.eval a c7394 := derived7394 a h
  have h2 : Entails.eval a c8829 := derived8829 a h
  have h3 : Entails.eval a c8779 := derived8779 a h
  have h4 : Entails.eval a c8828 := derived8828 a h
  have h5 : Entails.eval a c8830 := derived8830 a h
  have h6 : Entails.eval a c7454 := derived7454 a h
  have h7 : Entails.eval a c8818 := derived8818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8832 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8810, some c8795, some c8670, some c8819, some c8823, some c8826, some c8779, some c8827, some c7394, some c8828, some c8829, some c8831, some c727, some c1419, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8832 : lratChecker f8832 p8832 = .success := by decide +kernel
theorem unsat8832 : Unsatisfiable (PosFin 65) f8832 := by
  apply lratCheckerSound f8832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8832
  · intro a ha; simp [p8832] at ha; subst a; trivial
  · exact checked8832
theorem derived8832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8832 := by
  apply localUnsat_implies_entails f8832 [c8810, c8795, c8670, c8819, c8823, c8826, c8779, c8827, c7394, c8828, c8829, c8831, c727, c1419] c8832 unsat8832 (by rfl) a
  have h0 : Entails.eval a c8810 := derived8810 a h
  have h1 : Entails.eval a c8795 := derived8795 a h
  have h2 : Entails.eval a c8670 := derived8670 a h
  have h3 : Entails.eval a c8819 := derived8819 a h
  have h4 : Entails.eval a c8823 := derived8823 a h
  have h5 : Entails.eval a c8826 := derived8826 a h
  have h6 : Entails.eval a c8779 := derived8779 a h
  have h7 : Entails.eval a c8827 := derived8827 a h
  have h8 : Entails.eval a c7394 := derived7394 a h
  have h9 : Entails.eval a c8828 := derived8828 a h
  have h10 : Entails.eval a c8829 := derived8829 a h
  have h11 : Entails.eval a c8831 := derived8831 a h
  have h12 : Entails.eval a c727 := h 726 (by decide)
  have h13 : Entails.eval a c1419 := h 1418 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8833 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7627, some c7676, some c7677, some c7670, some c1443, some c1450, some c1437, some c1449, some c1421, some c1408, some c1410, some c6704, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p8833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8833 : lratChecker f8833 p8833 = .success := by decide +kernel
theorem unsat8833 : Unsatisfiable (PosFin 65) f8833 := by
  apply lratCheckerSound f8833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8833
  · intro a ha; simp [p8833] at ha; subst a; trivial
  · exact checked8833
theorem derived8833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8833 := by
  apply localUnsat_implies_entails f8833 [c7627, c7676, c7677, c7670, c1443, c1450, c1437, c1449, c1421, c1408, c1410, c6704] c8833 unsat8833 (by rfl) a
  have h0 : Entails.eval a c7627 := derived7627 a h
  have h1 : Entails.eval a c7676 := derived7676 a h
  have h2 : Entails.eval a c7677 := derived7677 a h
  have h3 : Entails.eval a c7670 := derived7670 a h
  have h4 : Entails.eval a c1443 := h 1442 (by decide)
  have h5 : Entails.eval a c1450 := h 1449 (by decide)
  have h6 : Entails.eval a c1437 := h 1436 (by decide)
  have h7 : Entails.eval a c1449 := h 1448 (by decide)
  have h8 : Entails.eval a c1421 := h 1420 (by decide)
  have h9 : Entails.eval a c1408 := h 1407 (by decide)
  have h10 : Entails.eval a c1410 := h 1409 (by decide)
  have h11 : Entails.eval a c6704 := derived6704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8834 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8832, some c8810, some c8795, some c8670, some c8718, some c8833, some c7689, some c7646, some c7791, some c7688, some c7805, some c7657, some c7768, some c1450, some c1437, some c1449, some c1421, some c1408, some c1410, some c6704, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8834 : lratChecker f8834 p8834 = .success := by decide +kernel
theorem unsat8834 : Unsatisfiable (PosFin 65) f8834 := by
  apply lratCheckerSound f8834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8834
  · intro a ha; simp [p8834] at ha; subst a; trivial
  · exact checked8834
theorem derived8834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8834 := by
  apply localUnsat_implies_entails f8834 [c8832, c8810, c8795, c8670, c8718, c8833, c7689, c7646, c7791, c7688, c7805, c7657, c7768, c1450, c1437, c1449, c1421, c1408, c1410, c6704] c8834 unsat8834 (by rfl) a
  have h0 : Entails.eval a c8832 := derived8832 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c8795 := derived8795 a h
  have h3 : Entails.eval a c8670 := derived8670 a h
  have h4 : Entails.eval a c8718 := derived8718 a h
  have h5 : Entails.eval a c8833 := derived8833 a h
  have h6 : Entails.eval a c7689 := derived7689 a h
  have h7 : Entails.eval a c7646 := derived7646 a h
  have h8 : Entails.eval a c7791 := derived7791 a h
  have h9 : Entails.eval a c7688 := derived7688 a h
  have h10 : Entails.eval a c7805 := derived7805 a h
  have h11 : Entails.eval a c7657 := derived7657 a h
  have h12 : Entails.eval a c7768 := derived7768 a h
  have h13 : Entails.eval a c1450 := h 1449 (by decide)
  have h14 : Entails.eval a c1437 := h 1436 (by decide)
  have h15 : Entails.eval a c1449 := h 1448 (by decide)
  have h16 : Entails.eval a c1421 := h 1420 (by decide)
  have h17 : Entails.eval a c1408 := h 1407 (by decide)
  have h18 : Entails.eval a c1410 := h 1409 (by decide)
  have h19 : Entails.eval a c6704 := derived6704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8835 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8707, some c8722, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8835 : lratChecker f8835 p8835 = .success := by decide +kernel
theorem unsat8835 : Unsatisfiable (PosFin 65) f8835 := by
  apply lratCheckerSound f8835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8835
  · intro a ha; simp [p8835] at ha; subst a; trivial
  · exact checked8835
theorem derived8835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8835 := by
  apply localUnsat_implies_entails f8835 [c8707, c8722] c8835 unsat8835 (by rfl) a
  have h0 : Entails.eval a c8707 := derived8707 a h
  have h1 : Entails.eval a c8722 := derived8722 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8836 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8832, some c8810, some c8834, some c8835, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8836 : lratChecker f8836 p8836 = .success := by decide +kernel
theorem unsat8836 : Unsatisfiable (PosFin 65) f8836 := by
  apply lratCheckerSound f8836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8836
  · intro a ha; simp [p8836] at ha; subst a; trivial
  · exact checked8836
theorem derived8836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8836 := by
  apply localUnsat_implies_entails f8836 [c8832, c8810, c8834, c8835] c8836 unsat8836 (by rfl) a
  have h0 : Entails.eval a c8832 := derived8832 a h
  have h1 : Entails.eval a c8810 := derived8810 a h
  have h2 : Entails.eval a c8834 := derived8834 a h
  have h3 : Entails.eval a c8835 := derived8835 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8837 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8814, some c7835, some c7791, some c805, some c7836, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8837 : lratChecker f8837 p8837 = .success := by decide +kernel
theorem unsat8837 : Unsatisfiable (PosFin 65) f8837 := by
  apply lratCheckerSound f8837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8837
  · intro a ha; simp [p8837] at ha; subst a; trivial
  · exact checked8837
theorem derived8837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8837 := by
  apply localUnsat_implies_entails f8837 [c8814, c7835, c7791, c805, c7836] c8837 unsat8837 (by rfl) a
  have h0 : Entails.eval a c8814 := derived8814 a h
  have h1 : Entails.eval a c7835 := derived7835 a h
  have h2 : Entails.eval a c7791 := derived7791 a h
  have h3 : Entails.eval a c805 := h 804 (by decide)
  have h4 : Entails.eval a c7836 := derived7836 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8838 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8836, some c8832, some c8810, some c8795, some c8670, some c8837, some c7356, some c7467, some c8789, some c7379, some c7710, some c1356, some c8577, some c1044, some c129, some c2681, some c1561, some c2568, some c158, some c2532, some c3206, some c107, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8838 : lratChecker f8838 p8838 = .success := by decide +kernel
theorem unsat8838 : Unsatisfiable (PosFin 65) f8838 := by
  apply lratCheckerSound f8838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8838
  · intro a ha; simp [p8838] at ha; subst a; trivial
  · exact checked8838
theorem derived8838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8838 := by
  apply localUnsat_implies_entails f8838 [c8836, c8832, c8810, c8795, c8670, c8837, c7356, c7467, c8789, c7379, c7710, c1356, c8577, c1044, c129, c2681, c1561, c2568, c158, c2532, c3206, c107] c8838 unsat8838 (by rfl) a
  have h0 : Entails.eval a c8836 := derived8836 a h
  have h1 : Entails.eval a c8832 := derived8832 a h
  have h2 : Entails.eval a c8810 := derived8810 a h
  have h3 : Entails.eval a c8795 := derived8795 a h
  have h4 : Entails.eval a c8670 := derived8670 a h
  have h5 : Entails.eval a c8837 := derived8837 a h
  have h6 : Entails.eval a c7356 := derived7356 a h
  have h7 : Entails.eval a c7467 := derived7467 a h
  have h8 : Entails.eval a c8789 := derived8789 a h
  have h9 : Entails.eval a c7379 := derived7379 a h
  have h10 : Entails.eval a c7710 := derived7710 a h
  have h11 : Entails.eval a c1356 := h 1355 (by decide)
  have h12 : Entails.eval a c8577 := derived8577 a h
  have h13 : Entails.eval a c1044 := h 1043 (by decide)
  have h14 : Entails.eval a c129 := h 128 (by decide)
  have h15 : Entails.eval a c2681 := h 2680 (by decide)
  have h16 : Entails.eval a c1561 := h 1560 (by decide)
  have h17 : Entails.eval a c2568 := h 2567 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c2532 := h 2531 (by decide)
  have h20 : Entails.eval a c3206 := h 3205 (by decide)
  have h21 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8839 : DefaultClause 65 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7565, some c7569, some c776, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p8839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8839 : lratChecker f8839 p8839 = .success := by decide +kernel
theorem unsat8839 : Unsatisfiable (PosFin 65) f8839 := by
  apply lratCheckerSound f8839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8839
  · intro a ha; simp [p8839] at ha; subst a; trivial
  · exact checked8839
theorem derived8839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8839 := by
  apply localUnsat_implies_entails f8839 [c7565, c7569, c776] c8839 unsat8839 (by rfl) a
  have h0 : Entails.eval a c7565 := derived7565 a h
  have h1 : Entails.eval a c7569 := derived7569 a h
  have h2 : Entails.eval a c776 := h 775 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8840 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8670, some c8795, some c8810, some c8832, some c8838, some c8839, some c7356, some c273, some c1624, some c1363, some c131, some c1050, some c1564, some c2052, some c160, some c1748, some c3332, some c109, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8840 : lratChecker f8840 p8840 = .success := by decide +kernel
theorem unsat8840 : Unsatisfiable (PosFin 65) f8840 := by
  apply lratCheckerSound f8840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8840
  · intro a ha; simp [p8840] at ha; subst a; trivial
  · exact checked8840
theorem derived8840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8840 := by
  apply localUnsat_implies_entails f8840 [c8670, c8795, c8810, c8832, c8838, c8839, c7356, c273, c1624, c1363, c131, c1050, c1564, c2052, c160, c1748, c3332, c109] c8840 unsat8840 (by rfl) a
  have h0 : Entails.eval a c8670 := derived8670 a h
  have h1 : Entails.eval a c8795 := derived8795 a h
  have h2 : Entails.eval a c8810 := derived8810 a h
  have h3 : Entails.eval a c8832 := derived8832 a h
  have h4 : Entails.eval a c8838 := derived8838 a h
  have h5 : Entails.eval a c8839 := derived8839 a h
  have h6 : Entails.eval a c7356 := derived7356 a h
  have h7 : Entails.eval a c273 := h 272 (by decide)
  have h8 : Entails.eval a c1624 := h 1623 (by decide)
  have h9 : Entails.eval a c1363 := h 1362 (by decide)
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c1050 := h 1049 (by decide)
  have h12 : Entails.eval a c1564 := h 1563 (by decide)
  have h13 : Entails.eval a c2052 := h 2051 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c1748 := h 1747 (by decide)
  have h16 : Entails.eval a c3332 := h 3331 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8841 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8036, some c8166, some c1258, some c1540, some c1653, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8841 : lratChecker f8841 p8841 = .success := by decide +kernel
theorem unsat8841 : Unsatisfiable (PosFin 65) f8841 := by
  apply lratCheckerSound f8841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8841
  · intro a ha; simp [p8841] at ha; subst a; trivial
  · exact checked8841
theorem derived8841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8841 := by
  apply localUnsat_implies_entails f8841 [c8036, c8166, c1258, c1540, c1653] c8841 unsat8841 (by rfl) a
  have h0 : Entails.eval a c8036 := derived8036 a h
  have h1 : Entails.eval a c8166 := derived8166 a h
  have h2 : Entails.eval a c1258 := h 1257 (by decide)
  have h3 : Entails.eval a c1540 := h 1539 (by decide)
  have h4 : Entails.eval a c1653 := h 1652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8842 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8374, some c8373, some c8375, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8842 : lratChecker f8842 p8842 = .success := by decide +kernel
theorem unsat8842 : Unsatisfiable (PosFin 65) f8842 := by
  apply lratCheckerSound f8842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8842
  · intro a ha; simp [p8842] at ha; subst a; trivial
  · exact checked8842
theorem derived8842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8842 := by
  apply localUnsat_implies_entails f8842 [c8374, c8373, c8375] c8842 unsat8842 (by rfl) a
  have h0 : Entails.eval a c8374 := derived8374 a h
  have h1 : Entails.eval a c8373 := derived8373 a h
  have h2 : Entails.eval a c8375 := derived8375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8843 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8102, some c8133, some c8142, some c1492, some c1493, some c8842, some c8036, some c8841, some c8148, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8843 : lratChecker f8843 p8843 = .success := by decide +kernel
theorem unsat8843 : Unsatisfiable (PosFin 65) f8843 := by
  apply lratCheckerSound f8843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8843
  · intro a ha; simp [p8843] at ha; subst a; trivial
  · exact checked8843
theorem derived8843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8843 := by
  apply localUnsat_implies_entails f8843 [c8840, c8102, c8133, c8142, c1492, c1493, c8842, c8036, c8841, c8148] c8843 unsat8843 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8102 := derived8102 a h
  have h2 : Entails.eval a c8133 := derived8133 a h
  have h3 : Entails.eval a c8142 := derived8142 a h
  have h4 : Entails.eval a c1492 := h 1491 (by decide)
  have h5 : Entails.eval a c1493 := h 1492 (by decide)
  have h6 : Entails.eval a c8842 := derived8842 a h
  have h7 : Entails.eval a c8036 := derived8036 a h
  have h8 : Entails.eval a c8841 := derived8841 a h
  have h9 : Entails.eval a c8148 := derived8148 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8844 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c970, some c1058, some c8347, some c2043, some c7976, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8844 : lratChecker f8844 p8844 = .success := by decide +kernel
theorem unsat8844 : Unsatisfiable (PosFin 65) f8844 := by
  apply lratCheckerSound f8844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8844
  · intro a ha; simp [p8844] at ha; subst a; trivial
  · exact checked8844
theorem derived8844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8844 := by
  apply localUnsat_implies_entails f8844 [c8376, c970, c1058, c8347, c2043, c7976] c8844 unsat8844 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c970 := h 969 (by decide)
  have h2 : Entails.eval a c1058 := h 1057 (by decide)
  have h3 : Entails.eval a c8347 := derived8347 a h
  have h4 : Entails.eval a c2043 := h 2042 (by decide)
  have h5 : Entails.eval a c7976 := derived7976 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8845 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1114, some c1112, some c1138, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8845 : lratChecker f8845 p8845 = .success := by decide +kernel
theorem unsat8845 : Unsatisfiable (PosFin 65) f8845 := by
  apply lratCheckerSound f8845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8845
  · intro a ha; simp [p8845] at ha; subst a; trivial
  · exact checked8845
theorem derived8845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8845 := by
  apply localUnsat_implies_entails f8845 [c1114, c1112, c1138] c8845 unsat8845 (by rfl) a
  have h0 : Entails.eval a c1114 := h 1113 (by decide)
  have h1 : Entails.eval a c1112 := h 1111 (by decide)
  have h2 : Entails.eval a c1138 := h 1137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8846 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1391, some c1071, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8846 : lratChecker f8846 p8846 = .success := by decide +kernel
theorem unsat8846 : Unsatisfiable (PosFin 65) f8846 := by
  apply lratCheckerSound f8846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8846
  · intro a ha; simp [p8846] at ha; subst a; trivial
  · exact checked8846
theorem derived8846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8846 := by
  apply localUnsat_implies_entails f8846 [c1391, c1071] c8846 unsat8846 (by rfl) a
  have h0 : Entails.eval a c1391 := h 1390 (by decide)
  have h1 : Entails.eval a c1071 := h 1070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8847 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8376, some c8844, some c970, some c1058, some c8347, some c2043, some c2018, some c2348, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8847 : lratChecker f8847 p8847 = .success := by decide +kernel
theorem unsat8847 : Unsatisfiable (PosFin 65) f8847 := by
  apply lratCheckerSound f8847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8847
  · intro a ha; simp [p8847] at ha; subst a; trivial
  · exact checked8847
theorem derived8847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8847 := by
  apply localUnsat_implies_entails f8847 [c8376, c8844, c970, c1058, c8347, c2043, c2018, c2348] c8847 unsat8847 (by rfl) a
  have h0 : Entails.eval a c8376 := derived8376 a h
  have h1 : Entails.eval a c8844 := derived8844 a h
  have h2 : Entails.eval a c970 := h 969 (by decide)
  have h3 : Entails.eval a c1058 := h 1057 (by decide)
  have h4 : Entails.eval a c8347 := derived8347 a h
  have h5 : Entails.eval a c2043 := h 2042 (by decide)
  have h6 : Entails.eval a c2018 := h 2017 (by decide)
  have h7 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8848 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c971, some c1060, some c2022, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8848 : lratChecker f8848 p8848 = .success := by decide +kernel
theorem unsat8848 : Unsatisfiable (PosFin 65) f8848 := by
  apply lratCheckerSound f8848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8848
  · intro a ha; simp [p8848] at ha; subst a; trivial
  · exact checked8848
theorem derived8848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8848 := by
  apply localUnsat_implies_entails f8848 [c971, c1060, c2022] c8848 unsat8848 (by rfl) a
  have h0 : Entails.eval a c971 := h 970 (by decide)
  have h1 : Entails.eval a c1060 := h 1059 (by decide)
  have h2 : Entails.eval a c2022 := h 2021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8849 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8845, some c8848, some c8846, some c1384, some c1056, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8849 : lratChecker f8849 p8849 = .success := by decide +kernel
theorem unsat8849 : Unsatisfiable (PosFin 65) f8849 := by
  apply lratCheckerSound f8849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8849
  · intro a ha; simp [p8849] at ha; subst a; trivial
  · exact checked8849
theorem derived8849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8849 := by
  apply localUnsat_implies_entails f8849 [c8845, c8848, c8846, c1384, c1056] c8849 unsat8849 (by rfl) a
  have h0 : Entails.eval a c8845 := derived8845 a h
  have h1 : Entails.eval a c8848 := derived8848 a h
  have h2 : Entails.eval a c8846 := derived8846 a h
  have h3 : Entails.eval a c1384 := h 1383 (by decide)
  have h4 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8850 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7657, some c8796, some c1125, some c1126, some c7903, some c1269, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8850 : lratChecker f8850 p8850 = .success := by decide +kernel
theorem unsat8850 : Unsatisfiable (PosFin 65) f8850 := by
  apply lratCheckerSound f8850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8850
  · intro a ha; simp [p8850] at ha; subst a; trivial
  · exact checked8850
theorem derived8850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8850 := by
  apply localUnsat_implies_entails f8850 [c7657, c8796, c1125, c1126, c7903, c1269] c8850 unsat8850 (by rfl) a
  have h0 : Entails.eval a c7657 := derived7657 a h
  have h1 : Entails.eval a c8796 := derived8796 a h
  have h2 : Entails.eval a c1125 := h 1124 (by decide)
  have h3 : Entails.eval a c1126 := h 1125 (by decide)
  have h4 : Entails.eval a c7903 := derived7903 a h
  have h5 : Entails.eval a c1269 := h 1268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8851 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8116, some c8166, some c1552, some c1547, some c1544, some c1550, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8851 : lratChecker f8851 p8851 = .success := by decide +kernel
theorem unsat8851 : Unsatisfiable (PosFin 65) f8851 := by
  apply lratCheckerSound f8851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8851
  · intro a ha; simp [p8851] at ha; subst a; trivial
  · exact checked8851
theorem derived8851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8851 := by
  apply localUnsat_implies_entails f8851 [c8116, c8166, c1552, c1547, c1544, c1550] c8851 unsat8851 (by rfl) a
  have h0 : Entails.eval a c8116 := derived8116 a h
  have h1 : Entails.eval a c8166 := derived8166 a h
  have h2 : Entails.eval a c1552 := h 1551 (by decide)
  have h3 : Entails.eval a c1547 := h 1546 (by decide)
  have h4 : Entails.eval a c1544 := h 1543 (by decide)
  have h5 : Entails.eval a c1550 := h 1549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8852 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8846, some c986, some c1077, some c2033, some c2036, some c2030, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8852 : lratChecker f8852 p8852 = .success := by decide +kernel
theorem unsat8852 : Unsatisfiable (PosFin 65) f8852 := by
  apply lratCheckerSound f8852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8852
  · intro a ha; simp [p8852] at ha; subst a; trivial
  · exact checked8852
theorem derived8852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8852 := by
  apply localUnsat_implies_entails f8852 [c8846, c986, c1077, c2033, c2036, c2030] c8852 unsat8852 (by rfl) a
  have h0 : Entails.eval a c8846 := derived8846 a h
  have h1 : Entails.eval a c986 := h 985 (by decide)
  have h2 : Entails.eval a c1077 := h 1076 (by decide)
  have h3 : Entails.eval a c2033 := h 2032 (by decide)
  have h4 : Entails.eval a c2036 := h 2035 (by decide)
  have h5 : Entails.eval a c2030 := h 2029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8853 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8840, some c8670, some c8843, some c8849, some c8376, some c8847, some c8347, some c8850, some c8852, some c8116, some c8851, some c8166, some c1533, some c1532, some c1534, some c1536, some c6760, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8853 : lratChecker f8853 p8853 = .success := by decide +kernel
theorem unsat8853 : Unsatisfiable (PosFin 65) f8853 := by
  apply lratCheckerSound f8853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8853
  · intro a ha; simp [p8853] at ha; subst a; trivial
  · exact checked8853
theorem derived8853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8853 := by
  apply localUnsat_implies_entails f8853 [c8840, c8670, c8843, c8849, c8376, c8847, c8347, c8850, c8852, c8116, c8851, c8166, c1533, c1532, c1534, c1536, c6760] c8853 unsat8853 (by rfl) a
  have h0 : Entails.eval a c8840 := derived8840 a h
  have h1 : Entails.eval a c8670 := derived8670 a h
  have h2 : Entails.eval a c8843 := derived8843 a h
  have h3 : Entails.eval a c8849 := derived8849 a h
  have h4 : Entails.eval a c8376 := derived8376 a h
  have h5 : Entails.eval a c8847 := derived8847 a h
  have h6 : Entails.eval a c8347 := derived8347 a h
  have h7 : Entails.eval a c8850 := derived8850 a h
  have h8 : Entails.eval a c8852 := derived8852 a h
  have h9 : Entails.eval a c8116 := derived8116 a h
  have h10 : Entails.eval a c8851 := derived8851 a h
  have h11 : Entails.eval a c8166 := derived8166 a h
  have h12 : Entails.eval a c1533 := h 1532 (by decide)
  have h13 : Entails.eval a c1532 := h 1531 (by decide)
  have h14 : Entails.eval a c1534 := h 1533 (by decide)
  have h15 : Entails.eval a c1536 := h 1535 (by decide)
  have h16 : Entails.eval a c6760 := derived6760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8854 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8002, some c8005, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8854 : lratChecker f8854 p8854 = .success := by decide +kernel
theorem unsat8854 : Unsatisfiable (PosFin 65) f8854 := by
  apply lratCheckerSound f8854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8854
  · intro a ha; simp [p8854] at ha; subst a; trivial
  · exact checked8854
theorem derived8854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8854 := by
  apply localUnsat_implies_entails f8854 [c8002, c8005] c8854 unsat8854 (by rfl) a
  have h0 : Entails.eval a c8002 := derived8002 a h
  have h1 : Entails.eval a c8005 := derived8005 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8855 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8623, some c1466, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8855 : lratChecker f8855 p8855 = .success := by decide +kernel
theorem unsat8855 : Unsatisfiable (PosFin 65) f8855 := by
  apply lratCheckerSound f8855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8855
  · intro a ha; simp [p8855] at ha; subst a; trivial
  · exact checked8855
theorem derived8855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8855 := by
  apply localUnsat_implies_entails f8855 [c8623, c1466] c8855 unsat8855 (by rfl) a
  have h0 : Entails.eval a c8623 := derived8623 a h
  have h1 : Entails.eval a c1466 := h 1465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8856 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1531, some c1517, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8856 : lratChecker f8856 p8856 = .success := by decide +kernel
theorem unsat8856 : Unsatisfiable (PosFin 65) f8856 := by
  apply lratCheckerSound f8856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8856
  · intro a ha; simp [p8856] at ha; subst a; trivial
  · exact checked8856
theorem derived8856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8856 := by
  apply localUnsat_implies_entails f8856 [c1531, c1517] c8856 unsat8856 (by rfl) a
  have h0 : Entails.eval a c1531 := h 1530 (by decide)
  have h1 : Entails.eval a c1517 := h 1516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8857 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8854, some c8855, some c8628, some c1483, some c1480, some c8856, some c8580, some c8157, some c8635, some c8633, some c459, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8857 : lratChecker f8857 p8857 = .success := by decide +kernel
theorem unsat8857 : Unsatisfiable (PosFin 65) f8857 := by
  apply lratCheckerSound f8857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8857
  · intro a ha; simp [p8857] at ha; subst a; trivial
  · exact checked8857
theorem derived8857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8857 := by
  apply localUnsat_implies_entails f8857 [c8854, c8855, c8628, c1483, c1480, c8856, c8580, c8157, c8635, c8633, c459] c8857 unsat8857 (by rfl) a
  have h0 : Entails.eval a c8854 := derived8854 a h
  have h1 : Entails.eval a c8855 := derived8855 a h
  have h2 : Entails.eval a c8628 := derived8628 a h
  have h3 : Entails.eval a c1483 := h 1482 (by decide)
  have h4 : Entails.eval a c1480 := h 1479 (by decide)
  have h5 : Entails.eval a c8856 := derived8856 a h
  have h6 : Entails.eval a c8580 := derived8580 a h
  have h7 : Entails.eval a c8157 := derived8157 a h
  have h8 : Entails.eval a c8635 := derived8635 a h
  have h9 : Entails.eval a c8633 := derived8633 a h
  have h10 : Entails.eval a c459 := h 458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8858 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8628, some c8856, some c1483, some c1487, some c8580, some c1480, some c8509, some c2340, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8858 : lratChecker f8858 p8858 = .success := by decide +kernel
theorem unsat8858 : Unsatisfiable (PosFin 65) f8858 := by
  apply lratCheckerSound f8858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8858
  · intro a ha; simp [p8858] at ha; subst a; trivial
  · exact checked8858
theorem derived8858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8858 := by
  apply localUnsat_implies_entails f8858 [c8628, c8856, c1483, c1487, c8580, c1480, c8509, c2340] c8858 unsat8858 (by rfl) a
  have h0 : Entails.eval a c8628 := derived8628 a h
  have h1 : Entails.eval a c8856 := derived8856 a h
  have h2 : Entails.eval a c1483 := h 1482 (by decide)
  have h3 : Entails.eval a c1487 := h 1486 (by decide)
  have h4 : Entails.eval a c8580 := derived8580 a h
  have h5 : Entails.eval a c1480 := h 1479 (by decide)
  have h6 : Entails.eval a c8509 := derived8509 a h
  have h7 : Entails.eval a c2340 := h 2339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8859 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1156, some c1157, some c1152, some c1151, some c1161, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8859 : lratChecker f8859 p8859 = .success := by decide +kernel
theorem unsat8859 : Unsatisfiable (PosFin 65) f8859 := by
  apply lratCheckerSound f8859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8859
  · intro a ha; simp [p8859] at ha; subst a; trivial
  · exact checked8859
theorem derived8859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8859 := by
  apply localUnsat_implies_entails f8859 [c1156, c1157, c1152, c1151, c1161] c8859 unsat8859 (by rfl) a
  have h0 : Entails.eval a c1156 := h 1155 (by decide)
  have h1 : Entails.eval a c1157 := h 1156 (by decide)
  have h2 : Entails.eval a c1152 := h 1151 (by decide)
  have h3 : Entails.eval a c1151 := h 1150 (by decide)
  have h4 : Entails.eval a c1161 := h 1160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8860 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8507, some c8098, some c2207, some c2212, some c2185, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8860 : lratChecker f8860 p8860 = .success := by decide +kernel
theorem unsat8860 : Unsatisfiable (PosFin 65) f8860 := by
  apply lratCheckerSound f8860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8860
  · intro a ha; simp [p8860] at ha; subst a; trivial
  · exact checked8860
theorem derived8860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8860 := by
  apply localUnsat_implies_entails f8860 [c8500, c8507, c8098, c2207, c2212, c2185] c8860 unsat8860 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8507 := derived8507 a h
  have h2 : Entails.eval a c8098 := derived8098 a h
  have h3 : Entails.eval a c2207 := h 2206 (by decide)
  have h4 : Entails.eval a c2212 := h 2211 (by decide)
  have h5 : Entails.eval a c2185 := h 2184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8861 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8858, some c8623, some c1478, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8861 : lratChecker f8861 p8861 = .success := by decide +kernel
theorem unsat8861 : Unsatisfiable (PosFin 65) f8861 := by
  apply lratCheckerSound f8861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8861
  · intro a ha; simp [p8861] at ha; subst a; trivial
  · exact checked8861
theorem derived8861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8861 := by
  apply localUnsat_implies_entails f8861 [c8858, c8623, c1478] c8861 unsat8861 (by rfl) a
  have h0 : Entails.eval a c8858 := derived8858 a h
  have h1 : Entails.eval a c8623 := derived8623 a h
  have h2 : Entails.eval a c1478 := h 1477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8862 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8857, some c8860, some c8861, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8862 : lratChecker f8862 p8862 = .success := by decide +kernel
theorem unsat8862 : Unsatisfiable (PosFin 65) f8862 := by
  apply lratCheckerSound f8862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8862
  · intro a ha; simp [p8862] at ha; subst a; trivial
  · exact checked8862
theorem derived8862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8862 := by
  apply localUnsat_implies_entails f8862 [c8857, c8860, c8861] c8862 unsat8862 (by rfl) a
  have h0 : Entails.eval a c8857 := derived8857 a h
  have h1 : Entails.eval a c8860 := derived8860 a h
  have h2 : Entails.eval a c8861 := derived8861 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8863 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2294, some c2304, some c2311, some c2302, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8863 : lratChecker f8863 p8863 = .success := by decide +kernel
theorem unsat8863 : Unsatisfiable (PosFin 65) f8863 := by
  apply lratCheckerSound f8863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8863
  · intro a ha; simp [p8863] at ha; subst a; trivial
  · exact checked8863
theorem derived8863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8863 := by
  apply localUnsat_implies_entails f8863 [c2294, c2304, c2311, c2302] c8863 unsat8863 (by rfl) a
  have h0 : Entails.eval a c2294 := h 2293 (by decide)
  have h1 : Entails.eval a c2304 := h 2303 (by decide)
  have h2 : Entails.eval a c2311 := h 2310 (by decide)
  have h3 : Entails.eval a c2302 := h 2301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8864 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1482, some c1481, some c1489, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8864 : lratChecker f8864 p8864 = .success := by decide +kernel
theorem unsat8864 : Unsatisfiable (PosFin 65) f8864 := by
  apply lratCheckerSound f8864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8864
  · intro a ha; simp [p8864] at ha; subst a; trivial
  · exact checked8864
theorem derived8864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8864 := by
  apply localUnsat_implies_entails f8864 [c1482, c1481, c1489] c8864 unsat8864 (by rfl) a
  have h0 : Entails.eval a c1482 := h 1481 (by decide)
  have h1 : Entails.eval a c1481 := h 1480 (by decide)
  have h2 : Entails.eval a c1489 := h 1488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8865 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8864, some c7922, some c1526, some c1517, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8865 : lratChecker f8865 p8865 = .success := by decide +kernel
theorem unsat8865 : Unsatisfiable (PosFin 65) f8865 := by
  apply lratCheckerSound f8865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8865
  · intro a ha; simp [p8865] at ha; subst a; trivial
  · exact checked8865
theorem derived8865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8865 := by
  apply localUnsat_implies_entails f8865 [c8864, c7922, c1526, c1517] c8865 unsat8865 (by rfl) a
  have h0 : Entails.eval a c8864 := derived8864 a h
  have h1 : Entails.eval a c7922 := derived7922 a h
  have h2 : Entails.eval a c1526 := h 1525 (by decide)
  have h3 : Entails.eval a c1517 := h 1516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8866 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8864, some c8865, some c1520, some c849, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8866 : lratChecker f8866 p8866 = .success := by decide +kernel
theorem unsat8866 : Unsatisfiable (PosFin 65) f8866 := by
  apply lratCheckerSound f8866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8866
  · intro a ha; simp [p8866] at ha; subst a; trivial
  · exact checked8866
theorem derived8866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8866 := by
  apply localUnsat_implies_entails f8866 [c8864, c8865, c1520, c849] c8866 unsat8866 (by rfl) a
  have h0 : Entails.eval a c8864 := derived8864 a h
  have h1 : Entails.eval a c8865 := derived8865 a h
  have h2 : Entails.eval a c1520 := h 1519 (by decide)
  have h3 : Entails.eval a c849 := h 848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8867 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8862, some c8659, some c8866, some c2336, some c2205, some c573, some c1156, some c1390, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8867 : lratChecker f8867 p8867 = .success := by decide +kernel
theorem unsat8867 : Unsatisfiable (PosFin 65) f8867 := by
  apply lratCheckerSound f8867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8867
  · intro a ha; simp [p8867] at ha; subst a; trivial
  · exact checked8867
theorem derived8867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8867 := by
  apply localUnsat_implies_entails f8867 [c8862, c8659, c8866, c2336, c2205, c573, c1156, c1390] c8867 unsat8867 (by rfl) a
  have h0 : Entails.eval a c8862 := derived8862 a h
  have h1 : Entails.eval a c8659 := derived8659 a h
  have h2 : Entails.eval a c8866 := derived8866 a h
  have h3 : Entails.eval a c2336 := h 2335 (by decide)
  have h4 : Entails.eval a c2205 := h 2204 (by decide)
  have h5 : Entails.eval a c573 := h 572 (by decide)
  have h6 : Entails.eval a c1156 := h 1155 (by decide)
  have h7 : Entails.eval a c1390 := h 1389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8868 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2201, some c2208, some c2191, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8868 : lratChecker f8868 p8868 = .success := by decide +kernel
theorem unsat8868 : Unsatisfiable (PosFin 65) f8868 := by
  apply lratCheckerSound f8868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8868
  · intro a ha; simp [p8868] at ha; subst a; trivial
  · exact checked8868
theorem derived8868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8868 := by
  apply localUnsat_implies_entails f8868 [c2201, c2208, c2191] c8868 unsat8868 (by rfl) a
  have h0 : Entails.eval a c2201 := h 2200 (by decide)
  have h1 : Entails.eval a c2208 := h 2207 (by decide)
  have h2 : Entails.eval a c2191 := h 2190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8869 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7961, some c2440, some c2439, some c2450, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8869 : lratChecker f8869 p8869 = .success := by decide +kernel
theorem unsat8869 : Unsatisfiable (PosFin 65) f8869 := by
  apply lratCheckerSound f8869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8869
  · intro a ha; simp [p8869] at ha; subst a; trivial
  · exact checked8869
theorem derived8869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8869 := by
  apply localUnsat_implies_entails f8869 [c7961, c2440, c2439, c2450] c8869 unsat8869 (by rfl) a
  have h0 : Entails.eval a c7961 := derived7961 a h
  have h1 : Entails.eval a c2440 := h 2439 (by decide)
  have h2 : Entails.eval a c2439 := h 2438 (by decide)
  have h3 : Entails.eval a c2450 := h 2449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8870 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8853, some c8840, some c8862, some c8670, some c8867, some c8546, some c8524, some c8098, some c8868, some c8869, some c1156, some c2411, some c92, some c115, some c1390, some c91, some c130, some c153, some c2511, some c3267, some c3271, some c99, some c3272, some c3269, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked8870 : lratChecker f8870 p8870 = .success := by decide +kernel
theorem unsat8870 : Unsatisfiable (PosFin 65) f8870 := by
  apply lratCheckerSound f8870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8870
  · intro a ha; simp [p8870] at ha; subst a; trivial
  · exact checked8870
theorem derived8870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8870 := by
  apply localUnsat_implies_entails f8870 [c8853, c8840, c8862, c8670, c8867, c8546, c8524, c8098, c8868, c8869, c1156, c2411, c92, c115, c1390, c91, c130, c153, c2511, c3267, c3271, c99, c3272, c3269] c8870 unsat8870 (by rfl) a
  have h0 : Entails.eval a c8853 := derived8853 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8862 := derived8862 a h
  have h3 : Entails.eval a c8670 := derived8670 a h
  have h4 : Entails.eval a c8867 := derived8867 a h
  have h5 : Entails.eval a c8546 := derived8546 a h
  have h6 : Entails.eval a c8524 := derived8524 a h
  have h7 : Entails.eval a c8098 := derived8098 a h
  have h8 : Entails.eval a c8868 := derived8868 a h
  have h9 : Entails.eval a c8869 := derived8869 a h
  have h10 : Entails.eval a c1156 := h 1155 (by decide)
  have h11 : Entails.eval a c2411 := h 2410 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c1390 := h 1389 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c130 := h 129 (by decide)
  have h17 : Entails.eval a c153 := h 152 (by decide)
  have h18 : Entails.eval a c2511 := h 2510 (by decide)
  have h19 : Entails.eval a c3267 := h 3266 (by decide)
  have h20 : Entails.eval a c3271 := h 3270 (by decide)
  have h21 : Entails.eval a c99 := h 98 (by decide)
  have h22 : Entails.eval a c3272 := h 3271 (by decide)
  have h23 : Entails.eval a c3269 := h 3268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8871 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8853, some c8840, some c8862, some c8870, some c8650, some c8575, some c1518, some c1512, some c1521, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8871 : lratChecker f8871 p8871 = .success := by decide +kernel
theorem unsat8871 : Unsatisfiable (PosFin 65) f8871 := by
  apply lratCheckerSound f8871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8871
  · intro a ha; simp [p8871] at ha; subst a; trivial
  · exact checked8871
theorem derived8871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8871 := by
  apply localUnsat_implies_entails f8871 [c8853, c8840, c8862, c8870, c8650, c8575, c1518, c1512, c1521] c8871 unsat8871 (by rfl) a
  have h0 : Entails.eval a c8853 := derived8853 a h
  have h1 : Entails.eval a c8840 := derived8840 a h
  have h2 : Entails.eval a c8862 := derived8862 a h
  have h3 : Entails.eval a c8870 := derived8870 a h
  have h4 : Entails.eval a c8650 := derived8650 a h
  have h5 : Entails.eval a c8575 := derived8575 a h
  have h6 : Entails.eval a c1518 := h 1517 (by decide)
  have h7 : Entails.eval a c1512 := h 1511 (by decide)
  have h8 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8872 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8628, some c8635, some c8633, some c8629, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8872 : lratChecker f8872 p8872 = .success := by decide +kernel
theorem unsat8872 : Unsatisfiable (PosFin 65) f8872 := by
  apply lratCheckerSound f8872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8872
  · intro a ha; simp [p8872] at ha; subst a; trivial
  · exact checked8872
theorem derived8872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8872 := by
  apply localUnsat_implies_entails f8872 [c8628, c8635, c8633, c8629] c8872 unsat8872 (by rfl) a
  have h0 : Entails.eval a c8628 := derived8628 a h
  have h1 : Entails.eval a c8635 := derived8635 a h
  have h2 : Entails.eval a c8633 := derived8633 a h
  have h3 : Entails.eval a c8629 := derived8629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8873 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8872, some c8580, some c8631, some c8629, some c8578, some c8593, some c580, some c1014, some c1392, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8873 : lratChecker f8873 p8873 = .success := by decide +kernel
theorem unsat8873 : Unsatisfiable (PosFin 65) f8873 := by
  apply lratCheckerSound f8873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8873
  · intro a ha; simp [p8873] at ha; subst a; trivial
  · exact checked8873
theorem derived8873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8873 := by
  apply localUnsat_implies_entails f8873 [c8872, c8580, c8631, c8629, c8578, c8593, c580, c1014, c1392] c8873 unsat8873 (by rfl) a
  have h0 : Entails.eval a c8872 := derived8872 a h
  have h1 : Entails.eval a c8580 := derived8580 a h
  have h2 : Entails.eval a c8631 := derived8631 a h
  have h3 : Entails.eval a c8629 := derived8629 a h
  have h4 : Entails.eval a c8578 := derived8578 a h
  have h5 : Entails.eval a c8593 := derived8593 a h
  have h6 : Entails.eval a c580 := h 579 (by decide)
  have h7 : Entails.eval a c1014 := h 1013 (by decide)
  have h8 : Entails.eval a c1392 := h 1391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8874 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1058, some c1394, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8874 : lratChecker f8874 p8874 = .success := by decide +kernel
theorem unsat8874 : Unsatisfiable (PosFin 65) f8874 := by
  apply lratCheckerSound f8874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8874
  · intro a ha; simp [p8874] at ha; subst a; trivial
  · exact checked8874
theorem derived8874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8874 := by
  apply localUnsat_implies_entails f8874 [c1058, c1394] c8874 unsat8874 (by rfl) a
  have h0 : Entails.eval a c1058 := h 1057 (by decide)
  have h1 : Entails.eval a c1394 := h 1393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8875 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8874, some c7827, some c8510, some c1553, some c1548, some c1537, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8875 : lratChecker f8875 p8875 = .success := by decide +kernel
theorem unsat8875 : Unsatisfiable (PosFin 65) f8875 := by
  apply lratCheckerSound f8875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8875
  · intro a ha; simp [p8875] at ha; subst a; trivial
  · exact checked8875
theorem derived8875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8875 := by
  apply localUnsat_implies_entails f8875 [c8874, c7827, c8510, c1553, c1548, c1537] c8875 unsat8875 (by rfl) a
  have h0 : Entails.eval a c8874 := derived8874 a h
  have h1 : Entails.eval a c7827 := derived7827 a h
  have h2 : Entails.eval a c8510 := derived8510 a h
  have h3 : Entails.eval a c1553 := h 1552 (by decide)
  have h4 : Entails.eval a c1548 := h 1547 (by decide)
  have h5 : Entails.eval a c1537 := h 1536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8876 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c970, some c1895, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p8876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8876 : lratChecker f8876 p8876 = .success := by decide +kernel
theorem unsat8876 : Unsatisfiable (PosFin 65) f8876 := by
  apply lratCheckerSound f8876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8876
  · intro a ha; simp [p8876] at ha; subst a; trivial
  · exact checked8876
theorem derived8876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8876 := by
  apply localUnsat_implies_entails f8876 [c970, c1895] c8876 unsat8876 (by rfl) a
  have h0 : Entails.eval a c970 := h 969 (by decide)
  have h1 : Entails.eval a c1895 := h 1894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8877 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1553, some c1548, some c1537, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p8877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8877 : lratChecker f8877 p8877 = .success := by decide +kernel
theorem unsat8877 : Unsatisfiable (PosFin 65) f8877 := by
  apply lratCheckerSound f8877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8877
  · intro a ha; simp [p8877] at ha; subst a; trivial
  · exact checked8877
theorem derived8877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8877 := by
  apply localUnsat_implies_entails f8877 [c1553, c1548, c1537] c8877 unsat8877 (by rfl) a
  have h0 : Entails.eval a c1553 := h 1552 (by decide)
  have h1 : Entails.eval a c1548 := h 1547 (by decide)
  have h2 : Entails.eval a c1537 := h 1536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8878 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨31, by decide⟩, true), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8877, some c852, some c1217, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8878 : lratChecker f8878 p8878 = .success := by decide +kernel
theorem unsat8878 : Unsatisfiable (PosFin 65) f8878 := by
  apply lratCheckerSound f8878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8878
  · intro a ha; simp [p8878] at ha; subst a; trivial
  · exact checked8878
theorem derived8878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8878 := by
  apply localUnsat_implies_entails f8878 [c8877, c852, c1217] c8878 unsat8878 (by rfl) a
  have h0 : Entails.eval a c8877 := derived8877 a h
  have h1 : Entails.eval a c852 := h 851 (by decide)
  have h2 : Entails.eval a c1217 := h 1216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8879 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8875, some c8098, some c8859, some c8852, some c8878, some c970, some c1221, some c1986, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8879 : lratChecker f8879 p8879 = .success := by decide +kernel
theorem unsat8879 : Unsatisfiable (PosFin 65) f8879 := by
  apply lratCheckerSound f8879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8879
  · intro a ha; simp [p8879] at ha; subst a; trivial
  · exact checked8879
theorem derived8879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8879 := by
  apply localUnsat_implies_entails f8879 [c8875, c8098, c8859, c8852, c8878, c970, c1221, c1986] c8879 unsat8879 (by rfl) a
  have h0 : Entails.eval a c8875 := derived8875 a h
  have h1 : Entails.eval a c8098 := derived8098 a h
  have h2 : Entails.eval a c8859 := derived8859 a h
  have h3 : Entails.eval a c8852 := derived8852 a h
  have h4 : Entails.eval a c8878 := derived8878 a h
  have h5 : Entails.eval a c970 := h 969 (by decide)
  have h6 : Entails.eval a c1221 := h 1220 (by decide)
  have h7 : Entails.eval a c1986 := h 1985 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8880 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8879, some c8873, some c8623, some c7439, some c1250, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8880 : lratChecker f8880 p8880 = .success := by decide +kernel
theorem unsat8880 : Unsatisfiable (PosFin 65) f8880 := by
  apply lratCheckerSound f8880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8880
  · intro a ha; simp [p8880] at ha; subst a; trivial
  · exact checked8880
theorem derived8880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8880 := by
  apply localUnsat_implies_entails f8880 [c8879, c8873, c8623, c7439, c1250] c8880 unsat8880 (by rfl) a
  have h0 : Entails.eval a c8879 := derived8879 a h
  have h1 : Entails.eval a c8873 := derived8873 a h
  have h2 : Entails.eval a c8623 := derived8623 a h
  have h3 : Entails.eval a c7439 := derived7439 a h
  have h4 : Entails.eval a c1250 := h 1249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8880

end CochromaticTwenty.Certificates.FixedCore1
