import MerLeanExperiment.Certificates.FixedCore1.Steps0800_0899

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6781 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3525, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6781 : lratChecker f6781 p6781 = .success := by decide +kernel
theorem unsat6781 : Unsatisfiable (PosFin 65) f6781 := by
  apply lratCheckerSound f6781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6781
  · intro a ha; simp [p6781] at ha; subst a; trivial
  · exact checked6781
theorem derived6781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6781 := by
  apply localUnsat_implies_entails f6781 [c6581, c3525] c6781 unsat6781 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3525 := h 3524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6782 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3529, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6782 : lratChecker f6782 p6782 = .success := by decide +kernel
theorem unsat6782 : Unsatisfiable (PosFin 65) f6782 := by
  apply lratCheckerSound f6782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6782
  · intro a ha; simp [p6782] at ha; subst a; trivial
  · exact checked6782
theorem derived6782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6782 := by
  apply localUnsat_implies_entails f6782 [c6581, c3529] c6782 unsat6782 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3529 := h 3528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6783 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3531, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6783 : lratChecker f6783 p6783 = .success := by decide +kernel
theorem unsat6783 : Unsatisfiable (PosFin 65) f6783 := by
  apply lratCheckerSound f6783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6783
  · intro a ha; simp [p6783] at ha; subst a; trivial
  · exact checked6783
theorem derived6783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6783 := by
  apply localUnsat_implies_entails f6783 [c6581, c3531] c6783 unsat6783 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3531 := h 3530 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6784 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, false), (⟨57, by decide⟩, true), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3544, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6784 : lratChecker f6784 p6784 = .success := by decide +kernel
theorem unsat6784 : Unsatisfiable (PosFin 65) f6784 := by
  apply lratCheckerSound f6784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6784
  · intro a ha; simp [p6784] at ha; subst a; trivial
  · exact checked6784
theorem derived6784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6784 := by
  apply localUnsat_implies_entails f6784 [c6581, c3544] c6784 unsat6784 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3544 := h 3543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6785 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3551, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6785 : lratChecker f6785 p6785 = .success := by decide +kernel
theorem unsat6785 : Unsatisfiable (PosFin 65) f6785 := by
  apply lratCheckerSound f6785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6785
  · intro a ha; simp [p6785] at ha; subst a; trivial
  · exact checked6785
theorem derived6785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6785 := by
  apply localUnsat_implies_entails f6785 [c6581, c3551] c6785 unsat6785 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3551 := h 3550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6786 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3554, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6786 : lratChecker f6786 p6786 = .success := by decide +kernel
theorem unsat6786 : Unsatisfiable (PosFin 65) f6786 := by
  apply lratCheckerSound f6786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6786
  · intro a ha; simp [p6786] at ha; subst a; trivial
  · exact checked6786
theorem derived6786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6786 := by
  apply localUnsat_implies_entails f6786 [c6581, c3554] c6786 unsat6786 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3554 := h 3553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6787 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨42, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3558, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6787 : lratChecker f6787 p6787 = .success := by decide +kernel
theorem unsat6787 : Unsatisfiable (PosFin 65) f6787 := by
  apply lratCheckerSound f6787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6787
  · intro a ha; simp [p6787] at ha; subst a; trivial
  · exact checked6787
theorem derived6787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6787 := by
  apply localUnsat_implies_entails f6787 [c6581, c3558] c6787 unsat6787 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3558 := h 3557 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6788 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3561, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p6788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6788 : lratChecker f6788 p6788 = .success := by decide +kernel
theorem unsat6788 : Unsatisfiable (PosFin 65) f6788 := by
  apply lratCheckerSound f6788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6788
  · intro a ha; simp [p6788] at ha; subst a; trivial
  · exact checked6788
theorem derived6788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6788 := by
  apply localUnsat_implies_entails f6788 [c6581, c3561] c6788 unsat6788 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3561 := h 3560 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6789 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3571, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6789 : lratChecker f6789 p6789 = .success := by decide +kernel
theorem unsat6789 : Unsatisfiable (PosFin 65) f6789 := by
  apply lratCheckerSound f6789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6789
  · intro a ha; simp [p6789] at ha; subst a; trivial
  · exact checked6789
theorem derived6789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6789 := by
  apply localUnsat_implies_entails f6789 [c6581, c3571] c6789 unsat6789 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3571 := h 3570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6790 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3577, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6790 : lratChecker f6790 p6790 = .success := by decide +kernel
theorem unsat6790 : Unsatisfiable (PosFin 65) f6790 := by
  apply lratCheckerSound f6790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6790
  · intro a ha; simp [p6790] at ha; subst a; trivial
  · exact checked6790
theorem derived6790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6790 := by
  apply localUnsat_implies_entails f6790 [c6581, c3577] c6790 unsat6790 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3577 := h 3576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6791 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3579, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6791 : lratChecker f6791 p6791 = .success := by decide +kernel
theorem unsat6791 : Unsatisfiable (PosFin 65) f6791 := by
  apply lratCheckerSound f6791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6791
  · intro a ha; simp [p6791] at ha; subst a; trivial
  · exact checked6791
theorem derived6791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6791 := by
  apply localUnsat_implies_entails f6791 [c6581, c3579] c6791 unsat6791 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3579 := h 3578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6792 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3582, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6792 : lratChecker f6792 p6792 = .success := by decide +kernel
theorem unsat6792 : Unsatisfiable (PosFin 65) f6792 := by
  apply lratCheckerSound f6792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6792
  · intro a ha; simp [p6792] at ha; subst a; trivial
  · exact checked6792
theorem derived6792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6792 := by
  apply localUnsat_implies_entails f6792 [c6581, c3582] c6792 unsat6792 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3582 := h 3581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6793 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3592, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6793 : lratChecker f6793 p6793 = .success := by decide +kernel
theorem unsat6793 : Unsatisfiable (PosFin 65) f6793 := by
  apply lratCheckerSound f6793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6793
  · intro a ha; simp [p6793] at ha; subst a; trivial
  · exact checked6793
theorem derived6793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6793 := by
  apply localUnsat_implies_entails f6793 [c6581, c3592] c6793 unsat6793 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3592 := h 3591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6794 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3600, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6794 : lratChecker f6794 p6794 = .success := by decide +kernel
theorem unsat6794 : Unsatisfiable (PosFin 65) f6794 := by
  apply lratCheckerSound f6794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6794
  · intro a ha; simp [p6794] at ha; subst a; trivial
  · exact checked6794
theorem derived6794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6794 := by
  apply localUnsat_implies_entails f6794 [c6581, c3600] c6794 unsat6794 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3600 := h 3599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6795 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3624, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6795 : lratChecker f6795 p6795 = .success := by decide +kernel
theorem unsat6795 : Unsatisfiable (PosFin 65) f6795 := by
  apply lratCheckerSound f6795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6795
  · intro a ha; simp [p6795] at ha; subst a; trivial
  · exact checked6795
theorem derived6795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6795 := by
  apply localUnsat_implies_entails f6795 [c6581, c3624] c6795 unsat6795 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3624 := h 3623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6796 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3629, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6796 : lratChecker f6796 p6796 = .success := by decide +kernel
theorem unsat6796 : Unsatisfiable (PosFin 65) f6796 := by
  apply lratCheckerSound f6796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6796
  · intro a ha; simp [p6796] at ha; subst a; trivial
  · exact checked6796
theorem derived6796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6796 := by
  apply localUnsat_implies_entails f6796 [c6581, c3629] c6796 unsat6796 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3629 := h 3628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6797 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3633, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6797 : lratChecker f6797 p6797 = .success := by decide +kernel
theorem unsat6797 : Unsatisfiable (PosFin 65) f6797 := by
  apply lratCheckerSound f6797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6797
  · intro a ha; simp [p6797] at ha; subst a; trivial
  · exact checked6797
theorem derived6797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6797 := by
  apply localUnsat_implies_entails f6797 [c6581, c3633] c6797 unsat6797 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3633 := h 3632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6798 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨47, by decide⟩, true), (⟨62, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3636, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6798 : lratChecker f6798 p6798 = .success := by decide +kernel
theorem unsat6798 : Unsatisfiable (PosFin 65) f6798 := by
  apply lratCheckerSound f6798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6798
  · intro a ha; simp [p6798] at ha; subst a; trivial
  · exact checked6798
theorem derived6798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6798 := by
  apply localUnsat_implies_entails f6798 [c6581, c3636] c6798 unsat6798 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3636 := h 3635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6799 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3638, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6799 : lratChecker f6799 p6799 = .success := by decide +kernel
theorem unsat6799 : Unsatisfiable (PosFin 65) f6799 := by
  apply lratCheckerSound f6799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6799
  · intro a ha; simp [p6799] at ha; subst a; trivial
  · exact checked6799
theorem derived6799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6799 := by
  apply localUnsat_implies_entails f6799 [c6581, c3638] c6799 unsat6799 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3638 := h 3637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6800 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨45, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3653, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p6800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6800 : lratChecker f6800 p6800 = .success := by decide +kernel
theorem unsat6800 : Unsatisfiable (PosFin 65) f6800 := by
  apply lratCheckerSound f6800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6800
  · intro a ha; simp [p6800] at ha; subst a; trivial
  · exact checked6800
theorem derived6800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6800 := by
  apply localUnsat_implies_entails f6800 [c6581, c3653] c6800 unsat6800 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3653 := h 3652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6801 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3656, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6801 : lratChecker f6801 p6801 = .success := by decide +kernel
theorem unsat6801 : Unsatisfiable (PosFin 65) f6801 := by
  apply lratCheckerSound f6801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6801
  · intro a ha; simp [p6801] at ha; subst a; trivial
  · exact checked6801
theorem derived6801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6801 := by
  apply localUnsat_implies_entails f6801 [c6581, c3656] c6801 unsat6801 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3656 := h 3655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6802 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3694, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6802 : lratChecker f6802 p6802 = .success := by decide +kernel
theorem unsat6802 : Unsatisfiable (PosFin 65) f6802 := by
  apply lratCheckerSound f6802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6802
  · intro a ha; simp [p6802] at ha; subst a; trivial
  · exact checked6802
theorem derived6802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6802 := by
  apply localUnsat_implies_entails f6802 [c6581, c3694] c6802 unsat6802 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3694 := h 3693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6803 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3701, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6803 : lratChecker f6803 p6803 = .success := by decide +kernel
theorem unsat6803 : Unsatisfiable (PosFin 65) f6803 := by
  apply lratCheckerSound f6803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6803
  · intro a ha; simp [p6803] at ha; subst a; trivial
  · exact checked6803
theorem derived6803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6803 := by
  apply localUnsat_implies_entails f6803 [c6581, c3701] c6803 unsat6803 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3701 := h 3700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6804 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨39, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3711, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6804 : lratChecker f6804 p6804 = .success := by decide +kernel
theorem unsat6804 : Unsatisfiable (PosFin 65) f6804 := by
  apply lratCheckerSound f6804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6804
  · intro a ha; simp [p6804] at ha; subst a; trivial
  · exact checked6804
theorem derived6804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6804 := by
  apply localUnsat_implies_entails f6804 [c6581, c3711] c6804 unsat6804 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3711 := h 3710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6805 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨45, by decide⟩, true), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3715, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6805 : lratChecker f6805 p6805 = .success := by decide +kernel
theorem unsat6805 : Unsatisfiable (PosFin 65) f6805 := by
  apply lratCheckerSound f6805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6805
  · intro a ha; simp [p6805] at ha; subst a; trivial
  · exact checked6805
theorem derived6805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6805 := by
  apply localUnsat_implies_entails f6805 [c6581, c3715] c6805 unsat6805 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3715 := h 3714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6806 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨46, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3727, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6806 : lratChecker f6806 p6806 = .success := by decide +kernel
theorem unsat6806 : Unsatisfiable (PosFin 65) f6806 := by
  apply lratCheckerSound f6806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6806
  · intro a ha; simp [p6806] at ha; subst a; trivial
  · exact checked6806
theorem derived6806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6806 := by
  apply localUnsat_implies_entails f6806 [c6581, c3727] c6806 unsat6806 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3727 := h 3726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6807 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨40, by decide⟩, true), (⟨33, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3752, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6807 : lratChecker f6807 p6807 = .success := by decide +kernel
theorem unsat6807 : Unsatisfiable (PosFin 65) f6807 := by
  apply lratCheckerSound f6807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6807
  · intro a ha; simp [p6807] at ha; subst a; trivial
  · exact checked6807
theorem derived6807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6807 := by
  apply localUnsat_implies_entails f6807 [c6581, c3752] c6807 unsat6807 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3752 := h 3751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6808 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3801, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6808 : lratChecker f6808 p6808 = .success := by decide +kernel
theorem unsat6808 : Unsatisfiable (PosFin 65) f6808 := by
  apply lratCheckerSound f6808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6808
  · intro a ha; simp [p6808] at ha; subst a; trivial
  · exact checked6808
theorem derived6808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6808 := by
  apply localUnsat_implies_entails f6808 [c6581, c3801] c6808 unsat6808 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3801 := h 3800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6809 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨62, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3804, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6809 : lratChecker f6809 p6809 = .success := by decide +kernel
theorem unsat6809 : Unsatisfiable (PosFin 65) f6809 := by
  apply lratCheckerSound f6809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6809
  · intro a ha; simp [p6809] at ha; subst a; trivial
  · exact checked6809
theorem derived6809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6809 := by
  apply localUnsat_implies_entails f6809 [c6581, c3804] c6809 unsat6809 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3804 := h 3803 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6810 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨33, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3821, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6810 : lratChecker f6810 p6810 = .success := by decide +kernel
theorem unsat6810 : Unsatisfiable (PosFin 65) f6810 := by
  apply lratCheckerSound f6810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6810
  · intro a ha; simp [p6810] at ha; subst a; trivial
  · exact checked6810
theorem derived6810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6810 := by
  apply localUnsat_implies_entails f6810 [c6581, c3821] c6810 unsat6810 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3821 := h 3820 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6811 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨33, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3849, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6811 : lratChecker f6811 p6811 = .success := by decide +kernel
theorem unsat6811 : Unsatisfiable (PosFin 65) f6811 := by
  apply lratCheckerSound f6811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6811
  · intro a ha; simp [p6811] at ha; subst a; trivial
  · exact checked6811
theorem derived6811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6811 := by
  apply localUnsat_implies_entails f6811 [c6581, c3849] c6811 unsat6811 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3849 := h 3848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6812 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3852, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6812 : lratChecker f6812 p6812 = .success := by decide +kernel
theorem unsat6812 : Unsatisfiable (PosFin 65) f6812 := by
  apply lratCheckerSound f6812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6812
  · intro a ha; simp [p6812] at ha; subst a; trivial
  · exact checked6812
theorem derived6812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6812 := by
  apply localUnsat_implies_entails f6812 [c6581, c3852] c6812 unsat6812 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3852 := h 3851 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6813 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3858, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p6813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6813 : lratChecker f6813 p6813 = .success := by decide +kernel
theorem unsat6813 : Unsatisfiable (PosFin 65) f6813 := by
  apply lratCheckerSound f6813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6813
  · intro a ha; simp [p6813] at ha; subst a; trivial
  · exact checked6813
theorem derived6813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6813 := by
  apply localUnsat_implies_entails f6813 [c6581, c3858] c6813 unsat6813 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3858 := h 3857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6814 : DefaultClause 65 := directClause [(⟨43, by decide⟩, false), (⟨33, by decide⟩, false), (⟨56, by decide⟩, true), (⟨44, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3884, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6814 : lratChecker f6814 p6814 = .success := by decide +kernel
theorem unsat6814 : Unsatisfiable (PosFin 65) f6814 := by
  apply lratCheckerSound f6814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6814
  · intro a ha; simp [p6814] at ha; subst a; trivial
  · exact checked6814
theorem derived6814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6814 := by
  apply localUnsat_implies_entails f6814 [c6581, c3884] c6814 unsat6814 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3884 := h 3883 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6815 : DefaultClause 65 := directClause [(⟨33, by decide⟩, true), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3901, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6815 : lratChecker f6815 p6815 = .success := by decide +kernel
theorem unsat6815 : Unsatisfiable (PosFin 65) f6815 := by
  apply lratCheckerSound f6815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6815
  · intro a ha; simp [p6815] at ha; subst a; trivial
  · exact checked6815
theorem derived6815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6815 := by
  apply localUnsat_implies_entails f6815 [c6581, c3901] c6815 unsat6815 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3901 := h 3900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6816 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3930, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6816 : lratChecker f6816 p6816 = .success := by decide +kernel
theorem unsat6816 : Unsatisfiable (PosFin 65) f6816 := by
  apply lratCheckerSound f6816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6816
  · intro a ha; simp [p6816] at ha; subst a; trivial
  · exact checked6816
theorem derived6816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6816 := by
  apply localUnsat_implies_entails f6816 [c6581, c3930] c6816 unsat6816 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3930 := h 3929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6817 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3932, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6817 : lratChecker f6817 p6817 = .success := by decide +kernel
theorem unsat6817 : Unsatisfiable (PosFin 65) f6817 := by
  apply lratCheckerSound f6817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6817
  · intro a ha; simp [p6817] at ha; subst a; trivial
  · exact checked6817
theorem derived6817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6817 := by
  apply localUnsat_implies_entails f6817 [c6581, c3932] c6817 unsat6817 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3932 := h 3931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6818 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3938, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6818 : lratChecker f6818 p6818 = .success := by decide +kernel
theorem unsat6818 : Unsatisfiable (PosFin 65) f6818 := by
  apply lratCheckerSound f6818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6818
  · intro a ha; simp [p6818] at ha; subst a; trivial
  · exact checked6818
theorem derived6818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6818 := by
  apply localUnsat_implies_entails f6818 [c6581, c3938] c6818 unsat6818 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3938 := h 3937 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6819 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3947, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6819 : lratChecker f6819 p6819 = .success := by decide +kernel
theorem unsat6819 : Unsatisfiable (PosFin 65) f6819 := by
  apply lratCheckerSound f6819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6819
  · intro a ha; simp [p6819] at ha; subst a; trivial
  · exact checked6819
theorem derived6819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6819 := by
  apply localUnsat_implies_entails f6819 [c6581, c3947] c6819 unsat6819 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3947 := h 3946 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6820 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3952, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6820 : lratChecker f6820 p6820 = .success := by decide +kernel
theorem unsat6820 : Unsatisfiable (PosFin 65) f6820 := by
  apply lratCheckerSound f6820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6820
  · intro a ha; simp [p6820] at ha; subst a; trivial
  · exact checked6820
theorem derived6820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6820 := by
  apply localUnsat_implies_entails f6820 [c6581, c3952] c6820 unsat6820 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3952 := h 3951 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6821 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨56, by decide⟩, true), (⟨34, by decide⟩, true), (⟨49, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3953, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p6821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6821 : lratChecker f6821 p6821 = .success := by decide +kernel
theorem unsat6821 : Unsatisfiable (PosFin 65) f6821 := by
  apply lratCheckerSound f6821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6821
  · intro a ha; simp [p6821] at ha; subst a; trivial
  · exact checked6821
theorem derived6821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6821 := by
  apply localUnsat_implies_entails f6821 [c6581, c3953] c6821 unsat6821 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3953 := h 3952 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6822 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3965, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p6822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6822 : lratChecker f6822 p6822 = .success := by decide +kernel
theorem unsat6822 : Unsatisfiable (PosFin 65) f6822 := by
  apply lratCheckerSound f6822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6822
  · intro a ha; simp [p6822] at ha; subst a; trivial
  · exact checked6822
theorem derived6822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6822 := by
  apply localUnsat_implies_entails f6822 [c6581, c3965] c6822 unsat6822 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3965 := h 3964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6823 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3969, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6823 : lratChecker f6823 p6823 = .success := by decide +kernel
theorem unsat6823 : Unsatisfiable (PosFin 65) f6823 := by
  apply lratCheckerSound f6823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6823
  · intro a ha; simp [p6823] at ha; subst a; trivial
  · exact checked6823
theorem derived6823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6823 := by
  apply localUnsat_implies_entails f6823 [c6581, c3969] c6823 unsat6823 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3969 := h 3968 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6824 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3970, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6824 : lratChecker f6824 p6824 = .success := by decide +kernel
theorem unsat6824 : Unsatisfiable (PosFin 65) f6824 := by
  apply lratCheckerSound f6824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6824
  · intro a ha; simp [p6824] at ha; subst a; trivial
  · exact checked6824
theorem derived6824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6824 := by
  apply localUnsat_implies_entails f6824 [c6581, c3970] c6824 unsat6824 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3970 := h 3969 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6825 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3971, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6825 : lratChecker f6825 p6825 = .success := by decide +kernel
theorem unsat6825 : Unsatisfiable (PosFin 65) f6825 := by
  apply lratCheckerSound f6825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6825
  · intro a ha; simp [p6825] at ha; subst a; trivial
  · exact checked6825
theorem derived6825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6825 := by
  apply localUnsat_implies_entails f6825 [c6581, c3971] c6825 unsat6825 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3971 := h 3970 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6826 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3992, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6826 : lratChecker f6826 p6826 = .success := by decide +kernel
theorem unsat6826 : Unsatisfiable (PosFin 65) f6826 := by
  apply lratCheckerSound f6826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6826
  · intro a ha; simp [p6826] at ha; subst a; trivial
  · exact checked6826
theorem derived6826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6826 := by
  apply localUnsat_implies_entails f6826 [c6581, c3992] c6826 unsat6826 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3992 := h 3991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6827 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3993, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6827 : lratChecker f6827 p6827 = .success := by decide +kernel
theorem unsat6827 : Unsatisfiable (PosFin 65) f6827 := by
  apply lratCheckerSound f6827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6827
  · intro a ha; simp [p6827] at ha; subst a; trivial
  · exact checked6827
theorem derived6827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6827 := by
  apply localUnsat_implies_entails f6827 [c6581, c3993] c6827 unsat6827 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3993 := h 3992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6828 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3997, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6828 : lratChecker f6828 p6828 = .success := by decide +kernel
theorem unsat6828 : Unsatisfiable (PosFin 65) f6828 := by
  apply lratCheckerSound f6828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6828
  · intro a ha; simp [p6828] at ha; subst a; trivial
  · exact checked6828
theorem derived6828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6828 := by
  apply localUnsat_implies_entails f6828 [c6581, c3997] c6828 unsat6828 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3997 := h 3996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6829 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4004, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6829 : lratChecker f6829 p6829 = .success := by decide +kernel
theorem unsat6829 : Unsatisfiable (PosFin 65) f6829 := by
  apply lratCheckerSound f6829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6829
  · intro a ha; simp [p6829] at ha; subst a; trivial
  · exact checked6829
theorem derived6829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6829 := by
  apply localUnsat_implies_entails f6829 [c6581, c4004] c6829 unsat6829 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4004 := h 4003 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6830 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨36, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4012, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6830 : lratChecker f6830 p6830 = .success := by decide +kernel
theorem unsat6830 : Unsatisfiable (PosFin 65) f6830 := by
  apply lratCheckerSound f6830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6830
  · intro a ha; simp [p6830] at ha; subst a; trivial
  · exact checked6830
theorem derived6830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6830 := by
  apply localUnsat_implies_entails f6830 [c6581, c4012] c6830 unsat6830 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4012 := h 4011 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6831 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨36, by decide⟩, false), (⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4014, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6831 : lratChecker f6831 p6831 = .success := by decide +kernel
theorem unsat6831 : Unsatisfiable (PosFin 65) f6831 := by
  apply lratCheckerSound f6831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6831
  · intro a ha; simp [p6831] at ha; subst a; trivial
  · exact checked6831
theorem derived6831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6831 := by
  apply localUnsat_implies_entails f6831 [c6581, c4014] c6831 unsat6831 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4014 := h 4013 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6832 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4017, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6832 : lratChecker f6832 p6832 = .success := by decide +kernel
theorem unsat6832 : Unsatisfiable (PosFin 65) f6832 := by
  apply lratCheckerSound f6832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6832
  · intro a ha; simp [p6832] at ha; subst a; trivial
  · exact checked6832
theorem derived6832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6832 := by
  apply localUnsat_implies_entails f6832 [c6581, c4017] c6832 unsat6832 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4017 := h 4016 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6833 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨56, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4032, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6833 : lratChecker f6833 p6833 = .success := by decide +kernel
theorem unsat6833 : Unsatisfiable (PosFin 65) f6833 := by
  apply lratCheckerSound f6833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6833
  · intro a ha; simp [p6833] at ha; subst a; trivial
  · exact checked6833
theorem derived6833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6833 := by
  apply localUnsat_implies_entails f6833 [c6581, c4032] c6833 unsat6833 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4032 := h 4031 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6834 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4034, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6834 : lratChecker f6834 p6834 = .success := by decide +kernel
theorem unsat6834 : Unsatisfiable (PosFin 65) f6834 := by
  apply lratCheckerSound f6834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6834
  · intro a ha; simp [p6834] at ha; subst a; trivial
  · exact checked6834
theorem derived6834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6834 := by
  apply localUnsat_implies_entails f6834 [c6581, c4034] c6834 unsat6834 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4034 := h 4033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6835 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨42, by decide⟩, true), (⟨62, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4038, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6835 : lratChecker f6835 p6835 = .success := by decide +kernel
theorem unsat6835 : Unsatisfiable (PosFin 65) f6835 := by
  apply lratCheckerSound f6835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6835
  · intro a ha; simp [p6835] at ha; subst a; trivial
  · exact checked6835
theorem derived6835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6835 := by
  apply localUnsat_implies_entails f6835 [c6581, c4038] c6835 unsat6835 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4038 := h 4037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6836 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4040, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6836 : lratChecker f6836 p6836 = .success := by decide +kernel
theorem unsat6836 : Unsatisfiable (PosFin 65) f6836 := by
  apply lratCheckerSound f6836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6836
  · intro a ha; simp [p6836] at ha; subst a; trivial
  · exact checked6836
theorem derived6836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6836 := by
  apply localUnsat_implies_entails f6836 [c6581, c4040] c6836 unsat6836 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4040 := h 4039 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6837 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4042, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6837 : lratChecker f6837 p6837 = .success := by decide +kernel
theorem unsat6837 : Unsatisfiable (PosFin 65) f6837 := by
  apply lratCheckerSound f6837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6837
  · intro a ha; simp [p6837] at ha; subst a; trivial
  · exact checked6837
theorem derived6837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6837 := by
  apply localUnsat_implies_entails f6837 [c6581, c4042] c6837 unsat6837 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4042 := h 4041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6838 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4057, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6838 : lratChecker f6838 p6838 = .success := by decide +kernel
theorem unsat6838 : Unsatisfiable (PosFin 65) f6838 := by
  apply lratCheckerSound f6838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6838
  · intro a ha; simp [p6838] at ha; subst a; trivial
  · exact checked6838
theorem derived6838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6838 := by
  apply localUnsat_implies_entails f6838 [c6581, c4057] c6838 unsat6838 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4057 := h 4056 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6839 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4064, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6839 : lratChecker f6839 p6839 = .success := by decide +kernel
theorem unsat6839 : Unsatisfiable (PosFin 65) f6839 := by
  apply lratCheckerSound f6839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6839
  · intro a ha; simp [p6839] at ha; subst a; trivial
  · exact checked6839
theorem derived6839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6839 := by
  apply localUnsat_implies_entails f6839 [c6581, c4064] c6839 unsat6839 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4064 := h 4063 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6840 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4071, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6840 : lratChecker f6840 p6840 = .success := by decide +kernel
theorem unsat6840 : Unsatisfiable (PosFin 65) f6840 := by
  apply lratCheckerSound f6840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6840
  · intro a ha; simp [p6840] at ha; subst a; trivial
  · exact checked6840
theorem derived6840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6840 := by
  apply localUnsat_implies_entails f6840 [c6581, c4071] c6840 unsat6840 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4071 := h 4070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6841 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨34, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4093, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6841 : lratChecker f6841 p6841 = .success := by decide +kernel
theorem unsat6841 : Unsatisfiable (PosFin 65) f6841 := by
  apply lratCheckerSound f6841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6841
  · intro a ha; simp [p6841] at ha; subst a; trivial
  · exact checked6841
theorem derived6841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6841 := by
  apply localUnsat_implies_entails f6841 [c6581, c4093] c6841 unsat6841 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4093 := h 4092 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6842 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4110, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6842 : lratChecker f6842 p6842 = .success := by decide +kernel
theorem unsat6842 : Unsatisfiable (PosFin 65) f6842 := by
  apply lratCheckerSound f6842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6842
  · intro a ha; simp [p6842] at ha; subst a; trivial
  · exact checked6842
theorem derived6842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6842 := by
  apply localUnsat_implies_entails f6842 [c6581, c4110] c6842 unsat6842 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4110 := h 4109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6843 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨39, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4112, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6843 : lratChecker f6843 p6843 = .success := by decide +kernel
theorem unsat6843 : Unsatisfiable (PosFin 65) f6843 := by
  apply lratCheckerSound f6843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6843
  · intro a ha; simp [p6843] at ha; subst a; trivial
  · exact checked6843
theorem derived6843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6843 := by
  apply localUnsat_implies_entails f6843 [c6581, c4112] c6843 unsat6843 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4112 := h 4111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6844 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4131, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6844 : lratChecker f6844 p6844 = .success := by decide +kernel
theorem unsat6844 : Unsatisfiable (PosFin 65) f6844 := by
  apply lratCheckerSound f6844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6844
  · intro a ha; simp [p6844] at ha; subst a; trivial
  · exact checked6844
theorem derived6844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6844 := by
  apply localUnsat_implies_entails f6844 [c6581, c4131] c6844 unsat6844 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4131 := h 4130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6845 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4144, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6845 : lratChecker f6845 p6845 = .success := by decide +kernel
theorem unsat6845 : Unsatisfiable (PosFin 65) f6845 := by
  apply lratCheckerSound f6845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6845
  · intro a ha; simp [p6845] at ha; subst a; trivial
  · exact checked6845
theorem derived6845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6845 := by
  apply localUnsat_implies_entails f6845 [c6581, c4144] c6845 unsat6845 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4144 := h 4143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6846 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨60, by decide⟩, true), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4149, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6846 : lratChecker f6846 p6846 = .success := by decide +kernel
theorem unsat6846 : Unsatisfiable (PosFin 65) f6846 := by
  apply lratCheckerSound f6846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6846
  · intro a ha; simp [p6846] at ha; subst a; trivial
  · exact checked6846
theorem derived6846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6846 := by
  apply localUnsat_implies_entails f6846 [c6581, c4149] c6846 unsat6846 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4149 := h 4148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6847 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4150, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6847 : lratChecker f6847 p6847 = .success := by decide +kernel
theorem unsat6847 : Unsatisfiable (PosFin 65) f6847 := by
  apply lratCheckerSound f6847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6847
  · intro a ha; simp [p6847] at ha; subst a; trivial
  · exact checked6847
theorem derived6847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6847 := by
  apply localUnsat_implies_entails f6847 [c6581, c4150] c6847 unsat6847 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4150 := h 4149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6848 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4155, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6848 : lratChecker f6848 p6848 = .success := by decide +kernel
theorem unsat6848 : Unsatisfiable (PosFin 65) f6848 := by
  apply lratCheckerSound f6848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6848
  · intro a ha; simp [p6848] at ha; subst a; trivial
  · exact checked6848
theorem derived6848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6848 := by
  apply localUnsat_implies_entails f6848 [c6581, c4155] c6848 unsat6848 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4155 := h 4154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6849 : DefaultClause 65 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4156, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6849 : lratChecker f6849 p6849 = .success := by decide +kernel
theorem unsat6849 : Unsatisfiable (PosFin 65) f6849 := by
  apply lratCheckerSound f6849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6849
  · intro a ha; simp [p6849] at ha; subst a; trivial
  · exact checked6849
theorem derived6849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6849 := by
  apply localUnsat_implies_entails f6849 [c6581, c4156] c6849 unsat6849 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4156 := h 4155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6850 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨40, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4167, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6850 : lratChecker f6850 p6850 = .success := by decide +kernel
theorem unsat6850 : Unsatisfiable (PosFin 65) f6850 := by
  apply lratCheckerSound f6850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6850
  · intro a ha; simp [p6850] at ha; subst a; trivial
  · exact checked6850
theorem derived6850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6850 := by
  apply localUnsat_implies_entails f6850 [c6581, c4167] c6850 unsat6850 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4167 := h 4166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6851 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4211, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p6851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6851 : lratChecker f6851 p6851 = .success := by decide +kernel
theorem unsat6851 : Unsatisfiable (PosFin 65) f6851 := by
  apply lratCheckerSound f6851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6851
  · intro a ha; simp [p6851] at ha; subst a; trivial
  · exact checked6851
theorem derived6851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6851 := by
  apply localUnsat_implies_entails f6851 [c6581, c4211] c6851 unsat6851 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4211 := h 4210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6852 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4229, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6852 : lratChecker f6852 p6852 = .success := by decide +kernel
theorem unsat6852 : Unsatisfiable (PosFin 65) f6852 := by
  apply lratCheckerSound f6852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6852
  · intro a ha; simp [p6852] at ha; subst a; trivial
  · exact checked6852
theorem derived6852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6852 := by
  apply localUnsat_implies_entails f6852 [c6581, c4229] c6852 unsat6852 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4229 := h 4228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6853 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4231, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6853 : lratChecker f6853 p6853 = .success := by decide +kernel
theorem unsat6853 : Unsatisfiable (PosFin 65) f6853 := by
  apply lratCheckerSound f6853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6853
  · intro a ha; simp [p6853] at ha; subst a; trivial
  · exact checked6853
theorem derived6853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6853 := by
  apply localUnsat_implies_entails f6853 [c6581, c4231] c6853 unsat6853 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4231 := h 4230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6854 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4247, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6854 : lratChecker f6854 p6854 = .success := by decide +kernel
theorem unsat6854 : Unsatisfiable (PosFin 65) f6854 := by
  apply lratCheckerSound f6854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6854
  · intro a ha; simp [p6854] at ha; subst a; trivial
  · exact checked6854
theorem derived6854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6854 := by
  apply localUnsat_implies_entails f6854 [c6581, c4247] c6854 unsat6854 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4247 := h 4246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6855 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4252, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6855 : lratChecker f6855 p6855 = .success := by decide +kernel
theorem unsat6855 : Unsatisfiable (PosFin 65) f6855 := by
  apply lratCheckerSound f6855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6855
  · intro a ha; simp [p6855] at ha; subst a; trivial
  · exact checked6855
theorem derived6855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6855 := by
  apply localUnsat_implies_entails f6855 [c6581, c4252] c6855 unsat6855 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4252 := h 4251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6856 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨34, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4255, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p6856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6856 : lratChecker f6856 p6856 = .success := by decide +kernel
theorem unsat6856 : Unsatisfiable (PosFin 65) f6856 := by
  apply lratCheckerSound f6856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6856
  · intro a ha; simp [p6856] at ha; subst a; trivial
  · exact checked6856
theorem derived6856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6856 := by
  apply localUnsat_implies_entails f6856 [c6581, c4255] c6856 unsat6856 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4255 := h 4254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6857 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4270, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p6857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6857 : lratChecker f6857 p6857 = .success := by decide +kernel
theorem unsat6857 : Unsatisfiable (PosFin 65) f6857 := by
  apply lratCheckerSound f6857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6857
  · intro a ha; simp [p6857] at ha; subst a; trivial
  · exact checked6857
theorem derived6857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6857 := by
  apply localUnsat_implies_entails f6857 [c6581, c4270] c6857 unsat6857 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4270 := h 4269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6858 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨46, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4276, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p6858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6858 : lratChecker f6858 p6858 = .success := by decide +kernel
theorem unsat6858 : Unsatisfiable (PosFin 65) f6858 := by
  apply lratCheckerSound f6858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6858
  · intro a ha; simp [p6858] at ha; subst a; trivial
  · exact checked6858
theorem derived6858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6858 := by
  apply localUnsat_implies_entails f6858 [c6581, c4276] c6858 unsat6858 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4276 := h 4275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6859 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4279, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6859 : lratChecker f6859 p6859 = .success := by decide +kernel
theorem unsat6859 : Unsatisfiable (PosFin 65) f6859 := by
  apply lratCheckerSound f6859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6859
  · intro a ha; simp [p6859] at ha; subst a; trivial
  · exact checked6859
theorem derived6859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6859 := by
  apply localUnsat_implies_entails f6859 [c6581, c4279] c6859 unsat6859 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4279 := h 4278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6860 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨56, by decide⟩, true), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4280, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6860 : lratChecker f6860 p6860 = .success := by decide +kernel
theorem unsat6860 : Unsatisfiable (PosFin 65) f6860 := by
  apply lratCheckerSound f6860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6860
  · intro a ha; simp [p6860] at ha; subst a; trivial
  · exact checked6860
theorem derived6860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6860 := by
  apply localUnsat_implies_entails f6860 [c6581, c4280] c6860 unsat6860 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4280 := h 4279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6861 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨44, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4282, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6861 : lratChecker f6861 p6861 = .success := by decide +kernel
theorem unsat6861 : Unsatisfiable (PosFin 65) f6861 := by
  apply lratCheckerSound f6861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6861
  · intro a ha; simp [p6861] at ha; subst a; trivial
  · exact checked6861
theorem derived6861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6861 := by
  apply localUnsat_implies_entails f6861 [c6581, c4282] c6861 unsat6861 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4282 := h 4281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6862 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4291, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6862 : lratChecker f6862 p6862 = .success := by decide +kernel
theorem unsat6862 : Unsatisfiable (PosFin 65) f6862 := by
  apply lratCheckerSound f6862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6862
  · intro a ha; simp [p6862] at ha; subst a; trivial
  · exact checked6862
theorem derived6862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6862 := by
  apply localUnsat_implies_entails f6862 [c6581, c4291] c6862 unsat6862 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4291 := h 4290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6863 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4299, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6863 : lratChecker f6863 p6863 = .success := by decide +kernel
theorem unsat6863 : Unsatisfiable (PosFin 65) f6863 := by
  apply lratCheckerSound f6863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6863
  · intro a ha; simp [p6863] at ha; subst a; trivial
  · exact checked6863
theorem derived6863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6863 := by
  apply localUnsat_implies_entails f6863 [c6581, c4299] c6863 unsat6863 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4299 := h 4298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6864 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4301, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6864 : lratChecker f6864 p6864 = .success := by decide +kernel
theorem unsat6864 : Unsatisfiable (PosFin 65) f6864 := by
  apply lratCheckerSound f6864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6864
  · intro a ha; simp [p6864] at ha; subst a; trivial
  · exact checked6864
theorem derived6864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6864 := by
  apply localUnsat_implies_entails f6864 [c6581, c4301] c6864 unsat6864 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4301 := h 4300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6865 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4310, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6865 : lratChecker f6865 p6865 = .success := by decide +kernel
theorem unsat6865 : Unsatisfiable (PosFin 65) f6865 := by
  apply lratCheckerSound f6865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6865
  · intro a ha; simp [p6865] at ha; subst a; trivial
  · exact checked6865
theorem derived6865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6865 := by
  apply localUnsat_implies_entails f6865 [c6581, c4310] c6865 unsat6865 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4310 := h 4309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6866 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨56, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4315, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6866 : lratChecker f6866 p6866 = .success := by decide +kernel
theorem unsat6866 : Unsatisfiable (PosFin 65) f6866 := by
  apply lratCheckerSound f6866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6866
  · intro a ha; simp [p6866] at ha; subst a; trivial
  · exact checked6866
theorem derived6866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6866 := by
  apply localUnsat_implies_entails f6866 [c6581, c4315] c6866 unsat6866 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4315 := h 4314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6867 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4336, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p6867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6867 : lratChecker f6867 p6867 = .success := by decide +kernel
theorem unsat6867 : Unsatisfiable (PosFin 65) f6867 := by
  apply lratCheckerSound f6867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6867
  · intro a ha; simp [p6867] at ha; subst a; trivial
  · exact checked6867
theorem derived6867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6867 := by
  apply localUnsat_implies_entails f6867 [c6581, c4336] c6867 unsat6867 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4336 := h 4335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6868 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨46, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4347, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6868 : lratChecker f6868 p6868 = .success := by decide +kernel
theorem unsat6868 : Unsatisfiable (PosFin 65) f6868 := by
  apply lratCheckerSound f6868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6868
  · intro a ha; simp [p6868] at ha; subst a; trivial
  · exact checked6868
theorem derived6868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6868 := by
  apply localUnsat_implies_entails f6868 [c6581, c4347] c6868 unsat6868 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4347 := h 4346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6869 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨37, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4379, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p6869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6869 : lratChecker f6869 p6869 = .success := by decide +kernel
theorem unsat6869 : Unsatisfiable (PosFin 65) f6869 := by
  apply lratCheckerSound f6869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6869
  · intro a ha; simp [p6869] at ha; subst a; trivial
  · exact checked6869
theorem derived6869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6869 := by
  apply localUnsat_implies_entails f6869 [c6581, c4379] c6869 unsat6869 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4379 := h 4378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6870 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨44, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4381, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6870 : lratChecker f6870 p6870 = .success := by decide +kernel
theorem unsat6870 : Unsatisfiable (PosFin 65) f6870 := by
  apply lratCheckerSound f6870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6870
  · intro a ha; simp [p6870] at ha; subst a; trivial
  · exact checked6870
theorem derived6870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6870 := by
  apply localUnsat_implies_entails f6870 [c6581, c4381] c6870 unsat6870 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4381 := h 4380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6871 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4383, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p6871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6871 : lratChecker f6871 p6871 = .success := by decide +kernel
theorem unsat6871 : Unsatisfiable (PosFin 65) f6871 := by
  apply lratCheckerSound f6871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6871
  · intro a ha; simp [p6871] at ha; subst a; trivial
  · exact checked6871
theorem derived6871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6871 := by
  apply localUnsat_implies_entails f6871 [c6581, c4383] c6871 unsat6871 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4383 := h 4382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6872 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4384, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p6872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6872 : lratChecker f6872 p6872 = .success := by decide +kernel
theorem unsat6872 : Unsatisfiable (PosFin 65) f6872 := by
  apply lratCheckerSound f6872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6872
  · intro a ha; simp [p6872] at ha; subst a; trivial
  · exact checked6872
theorem derived6872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6872 := by
  apply localUnsat_implies_entails f6872 [c6581, c4384] c6872 unsat6872 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4384 := h 4383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6873 : DefaultClause 65 := directClause [(⟨57, by decide⟩, true), (⟨54, by decide⟩, true), (⟨37, by decide⟩, true), (⟨44, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4391, some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6873 : lratChecker f6873 p6873 = .success := by decide +kernel
theorem unsat6873 : Unsatisfiable (PosFin 65) f6873 := by
  apply lratCheckerSound f6873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6873
  · intro a ha; simp [p6873] at ha; subst a; trivial
  · exact checked6873
theorem derived6873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6873 := by
  apply localUnsat_implies_entails f6873 [c6581, c4391] c6873 unsat6873 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4391 := h 4390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6874 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4399, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6874 : lratChecker f6874 p6874 = .success := by decide +kernel
theorem unsat6874 : Unsatisfiable (PosFin 65) f6874 := by
  apply lratCheckerSound f6874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6874
  · intro a ha; simp [p6874] at ha; subst a; trivial
  · exact checked6874
theorem derived6874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6874 := by
  apply localUnsat_implies_entails f6874 [c6581, c4399] c6874 unsat6874 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4399 := h 4398 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6875 : DefaultClause 65 := directClause [(⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨62, by decide⟩, true), (⟨49, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4403, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6875 : lratChecker f6875 p6875 = .success := by decide +kernel
theorem unsat6875 : Unsatisfiable (PosFin 65) f6875 := by
  apply lratCheckerSound f6875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6875
  · intro a ha; simp [p6875] at ha; subst a; trivial
  · exact checked6875
theorem derived6875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6875 := by
  apply localUnsat_implies_entails f6875 [c6581, c4403] c6875 unsat6875 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4403 := h 4402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6876 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4408, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6876 : lratChecker f6876 p6876 = .success := by decide +kernel
theorem unsat6876 : Unsatisfiable (PosFin 65) f6876 := by
  apply lratCheckerSound f6876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6876
  · intro a ha; simp [p6876] at ha; subst a; trivial
  · exact checked6876
theorem derived6876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6876 := by
  apply localUnsat_implies_entails f6876 [c6581, c4408] c6876 unsat6876 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4408 := h 4407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6877 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨47, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4413, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p6877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6877 : lratChecker f6877 p6877 = .success := by decide +kernel
theorem unsat6877 : Unsatisfiable (PosFin 65) f6877 := by
  apply lratCheckerSound f6877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6877
  · intro a ha; simp [p6877] at ha; subst a; trivial
  · exact checked6877
theorem derived6877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6877 := by
  apply localUnsat_implies_entails f6877 [c6581, c4413] c6877 unsat6877 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4413 := h 4412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6878 : DefaultClause 65 := directClause [(⟨60, by decide⟩, true), (⟨47, by decide⟩, true), (⟨62, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4415, some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p6878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6878 : lratChecker f6878 p6878 = .success := by decide +kernel
theorem unsat6878 : Unsatisfiable (PosFin 65) f6878 := by
  apply lratCheckerSound f6878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6878
  · intro a ha; simp [p6878] at ha; subst a; trivial
  · exact checked6878
theorem derived6878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6878 := by
  apply localUnsat_implies_entails f6878 [c6581, c4415] c6878 unsat6878 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4415 := h 4414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6879 : DefaultClause 65 := directClause [(⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4416, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6879 : lratChecker f6879 p6879 = .success := by decide +kernel
theorem unsat6879 : Unsatisfiable (PosFin 65) f6879 := by
  apply lratCheckerSound f6879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6879
  · intro a ha; simp [p6879] at ha; subst a; trivial
  · exact checked6879
theorem derived6879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6879 := by
  apply localUnsat_implies_entails f6879 [c6581, c4416] c6879 unsat6879 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4416 := h 4415 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6880 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨60, by decide⟩, true), (⟨41, by decide⟩, true), (⟨38, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c4425, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6880 : lratChecker f6880 p6880 = .success := by decide +kernel
theorem unsat6880 : Unsatisfiable (PosFin 65) f6880 := by
  apply lratCheckerSound f6880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6880
  · intro a ha; simp [p6880] at ha; subst a; trivial
  · exact checked6880
theorem derived6880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6880 := by
  apply localUnsat_implies_entails f6880 [c6581, c4425] c6880 unsat6880 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c4425 := h 4424 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived6880

end CochromaticTwenty.Certificates.FixedCore1
