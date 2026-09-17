import MerLeanExperiment.Certificates.FixedCore1.Steps0700_0799

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c6681 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c60, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6681 : lratChecker f6681 p6681 = .success := by decide +kernel
theorem unsat6681 : Unsatisfiable (PosFin 65) f6681 := by
  apply lratCheckerSound f6681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6681
  · intro a ha; simp [p6681] at ha; subst a; trivial
  · exact checked6681
theorem derived6681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6681 := by
  apply localUnsat_implies_entails f6681 [c6581, c60] c6681 unsat6681 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6682 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c63, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6682 : lratChecker f6682 p6682 = .success := by decide +kernel
theorem unsat6682 : Unsatisfiable (PosFin 65) f6682 := by
  apply lratCheckerSound f6682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6682
  · intro a ha; simp [p6682] at ha; subst a; trivial
  · exact checked6682
theorem derived6682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6682 := by
  apply localUnsat_implies_entails f6682 [c6581, c63] c6682 unsat6682 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6683 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c65, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6683 : lratChecker f6683 p6683 = .success := by decide +kernel
theorem unsat6683 : Unsatisfiable (PosFin 65) f6683 := by
  apply lratCheckerSound f6683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6683
  · intro a ha; simp [p6683] at ha; subst a; trivial
  · exact checked6683
theorem derived6683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6683 := by
  apply localUnsat_implies_entails f6683 [c6581, c65] c6683 unsat6683 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6684 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨57, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c66, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6684 : lratChecker f6684 p6684 = .success := by decide +kernel
theorem unsat6684 : Unsatisfiable (PosFin 65) f6684 := by
  apply lratCheckerSound f6684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6684
  · intro a ha; simp [p6684] at ha; subst a; trivial
  · exact checked6684
theorem derived6684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6684 := by
  apply localUnsat_implies_entails f6684 [c6581, c66] c6684 unsat6684 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6685 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c68, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6685 : lratChecker f6685 p6685 = .success := by decide +kernel
theorem unsat6685 : Unsatisfiable (PosFin 65) f6685 := by
  apply lratCheckerSound f6685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6685
  · intro a ha; simp [p6685] at ha; subst a; trivial
  · exact checked6685
theorem derived6685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6685 := by
  apply localUnsat_implies_entails f6685 [c6581, c68] c6685 unsat6685 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6686 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, false), (⟨25, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c71, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6686 : lratChecker f6686 p6686 = .success := by decide +kernel
theorem unsat6686 : Unsatisfiable (PosFin 65) f6686 := by
  apply lratCheckerSound f6686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6686
  · intro a ha; simp [p6686] at ha; subst a; trivial
  · exact checked6686
theorem derived6686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6686 := by
  apply localUnsat_implies_entails f6686 [c6581, c71] c6686 unsat6686 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6687 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false), (⟨50, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c74, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6687 : lratChecker f6687 p6687 = .success := by decide +kernel
theorem unsat6687 : Unsatisfiable (PosFin 65) f6687 := by
  apply lratCheckerSound f6687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6687
  · intro a ha; simp [p6687] at ha; subst a; trivial
  · exact checked6687
theorem derived6687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6687 := by
  apply localUnsat_implies_entails f6687 [c6581, c74] c6687 unsat6687 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6688 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨2, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c212, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6688 : lratChecker f6688 p6688 = .success := by decide +kernel
theorem unsat6688 : Unsatisfiable (PosFin 65) f6688 := by
  apply lratCheckerSound f6688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6688
  · intro a ha; simp [p6688] at ha; subst a; trivial
  · exact checked6688
theorem derived6688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6688 := by
  apply localUnsat_implies_entails f6688 [c6581, c212] c6688 unsat6688 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6689 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨2, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c213, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6689 : lratChecker f6689 p6689 = .success := by decide +kernel
theorem unsat6689 : Unsatisfiable (PosFin 65) f6689 := by
  apply lratCheckerSound f6689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6689
  · intro a ha; simp [p6689] at ha; subst a; trivial
  · exact checked6689
theorem derived6689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6689 := by
  apply localUnsat_implies_entails f6689 [c6581, c213] c6689 unsat6689 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6690 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c215, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6690 : lratChecker f6690 p6690 = .success := by decide +kernel
theorem unsat6690 : Unsatisfiable (PosFin 65) f6690 := by
  apply lratCheckerSound f6690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6690
  · intro a ha; simp [p6690] at ha; subst a; trivial
  · exact checked6690
theorem derived6690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6690 := by
  apply localUnsat_implies_entails f6690 [c6581, c215] c6690 unsat6690 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6691 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c325, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6691 : lratChecker f6691 p6691 = .success := by decide +kernel
theorem unsat6691 : Unsatisfiable (PosFin 65) f6691 := by
  apply lratCheckerSound f6691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6691
  · intro a ha; simp [p6691] at ha; subst a; trivial
  · exact checked6691
theorem derived6691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6691 := by
  apply localUnsat_implies_entails f6691 [c6581, c325] c6691 unsat6691 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6692 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c329, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6692 : lratChecker f6692 p6692 = .success := by decide +kernel
theorem unsat6692 : Unsatisfiable (PosFin 65) f6692 := by
  apply lratCheckerSound f6692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6692
  · intro a ha; simp [p6692] at ha; subst a; trivial
  · exact checked6692
theorem derived6692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6692 := by
  apply localUnsat_implies_entails f6692 [c6581, c329] c6692 unsat6692 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6693 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c375, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6693 : lratChecker f6693 p6693 = .success := by decide +kernel
theorem unsat6693 : Unsatisfiable (PosFin 65) f6693 := by
  apply lratCheckerSound f6693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6693
  · intro a ha; simp [p6693] at ha; subst a; trivial
  · exact checked6693
theorem derived6693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6693 := by
  apply localUnsat_implies_entails f6693 [c6581, c375] c6693 unsat6693 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6694 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, true), (⟨3, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c377, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6694 : lratChecker f6694 p6694 = .success := by decide +kernel
theorem unsat6694 : Unsatisfiable (PosFin 65) f6694 := by
  apply lratCheckerSound f6694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6694
  · intro a ha; simp [p6694] at ha; subst a; trivial
  · exact checked6694
theorem derived6694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6694 := by
  apply localUnsat_implies_entails f6694 [c6581, c377] c6694 unsat6694 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6695 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨57, by decide⟩, true), (⟨3, by decide⟩, false), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c378, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6695 : lratChecker f6695 p6695 = .success := by decide +kernel
theorem unsat6695 : Unsatisfiable (PosFin 65) f6695 := by
  apply lratCheckerSound f6695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6695
  · intro a ha; simp [p6695] at ha; subst a; trivial
  · exact checked6695
theorem derived6695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6695 := by
  apply localUnsat_implies_entails f6695 [c6581, c378] c6695 unsat6695 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6696 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨1, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c648, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6696 : lratChecker f6696 p6696 = .success := by decide +kernel
theorem unsat6696 : Unsatisfiable (PosFin 65) f6696 := by
  apply lratCheckerSound f6696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6696
  · intro a ha; simp [p6696] at ha; subst a; trivial
  · exact checked6696
theorem derived6696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6696 := by
  apply localUnsat_implies_entails f6696 [c6581, c648] c6696 unsat6696 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c648 := h 647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6697 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c895, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6697 : lratChecker f6697 p6697 = .success := by decide +kernel
theorem unsat6697 : Unsatisfiable (PosFin 65) f6697 := by
  apply lratCheckerSound f6697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6697
  · intro a ha; simp [p6697] at ha; subst a; trivial
  · exact checked6697
theorem derived6697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6697 := by
  apply localUnsat_implies_entails f6697 [c6581, c895] c6697 unsat6697 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c895 := h 894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6698 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c949, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6698 : lratChecker f6698 p6698 = .success := by decide +kernel
theorem unsat6698 : Unsatisfiable (PosFin 65) f6698 := by
  apply lratCheckerSound f6698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6698
  · intro a ha; simp [p6698] at ha; subst a; trivial
  · exact checked6698
theorem derived6698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6698 := by
  apply localUnsat_implies_entails f6698 [c6581, c949] c6698 unsat6698 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c949 := h 948 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6699 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c950, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6699 : lratChecker f6699 p6699 = .success := by decide +kernel
theorem unsat6699 : Unsatisfiable (PosFin 65) f6699 := by
  apply lratCheckerSound f6699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6699
  · intro a ha; simp [p6699] at ha; subst a; trivial
  · exact checked6699
theorem derived6699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6699 := by
  apply localUnsat_implies_entails f6699 [c6581, c950] c6699 unsat6699 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c950 := h 949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6700 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c963, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6700 : lratChecker f6700 p6700 = .success := by decide +kernel
theorem unsat6700 : Unsatisfiable (PosFin 65) f6700 := by
  apply lratCheckerSound f6700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6700
  · intro a ha; simp [p6700] at ha; subst a; trivial
  · exact checked6700
theorem derived6700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6700 := by
  apply localUnsat_implies_entails f6700 [c6581, c963] c6700 unsat6700 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c963 := h 962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6701 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1194, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6701 : lratChecker f6701 p6701 = .success := by decide +kernel
theorem unsat6701 : Unsatisfiable (PosFin 65) f6701 := by
  apply lratCheckerSound f6701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6701
  · intro a ha; simp [p6701] at ha; subst a; trivial
  · exact checked6701
theorem derived6701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6701 := by
  apply localUnsat_implies_entails f6701 [c6581, c1194] c6701 unsat6701 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1194 := h 1193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6702 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1195, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6702 : lratChecker f6702 p6702 = .success := by decide +kernel
theorem unsat6702 : Unsatisfiable (PosFin 65) f6702 := by
  apply lratCheckerSound f6702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6702
  · intro a ha; simp [p6702] at ha; subst a; trivial
  · exact checked6702
theorem derived6702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6702 := by
  apply localUnsat_implies_entails f6702 [c6581, c1195] c6702 unsat6702 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1195 := h 1194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6703 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨12, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1298, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6703 : lratChecker f6703 p6703 = .success := by decide +kernel
theorem unsat6703 : Unsatisfiable (PosFin 65) f6703 := by
  apply lratCheckerSound f6703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6703
  · intro a ha; simp [p6703] at ha; subst a; trivial
  · exact checked6703
theorem derived6703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6703 := by
  apply localUnsat_implies_entails f6703 [c6581, c1298] c6703 unsat6703 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1298 := h 1297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6704 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨12, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1451, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6704 : lratChecker f6704 p6704 = .success := by decide +kernel
theorem unsat6704 : Unsatisfiable (PosFin 65) f6704 := by
  apply lratCheckerSound f6704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6704
  · intro a ha; simp [p6704] at ha; subst a; trivial
  · exact checked6704
theorem derived6704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6704 := by
  apply localUnsat_implies_entails f6704 [c6581, c1451] c6704 unsat6704 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1451 := h 1450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6705 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1498, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6705 : lratChecker f6705 p6705 = .success := by decide +kernel
theorem unsat6705 : Unsatisfiable (PosFin 65) f6705 := by
  apply lratCheckerSound f6705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6705
  · intro a ha; simp [p6705] at ha; subst a; trivial
  · exact checked6705
theorem derived6705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6705 := by
  apply localUnsat_implies_entails f6705 [c6581, c1498] c6705 unsat6705 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1498 := h 1497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6706 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1499, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6706 : lratChecker f6706 p6706 = .success := by decide +kernel
theorem unsat6706 : Unsatisfiable (PosFin 65) f6706 := by
  apply lratCheckerSound f6706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6706
  · intro a ha; simp [p6706] at ha; subst a; trivial
  · exact checked6706
theorem derived6706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6706 := by
  apply localUnsat_implies_entails f6706 [c6581, c1499] c6706 unsat6706 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1499 := h 1498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6707 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, false), (⟨56, by decide⟩, true), (⟨10, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1500, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6707 : lratChecker f6707 p6707 = .success := by decide +kernel
theorem unsat6707 : Unsatisfiable (PosFin 65) f6707 := by
  apply lratCheckerSound f6707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6707
  · intro a ha; simp [p6707] at ha; subst a; trivial
  · exact checked6707
theorem derived6707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6707 := by
  apply localUnsat_implies_entails f6707 [c6581, c1500] c6707 unsat6707 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6708 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1609, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6708 : lratChecker f6708 p6708 = .success := by decide +kernel
theorem unsat6708 : Unsatisfiable (PosFin 65) f6708 := by
  apply lratCheckerSound f6708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6708
  · intro a ha; simp [p6708] at ha; subst a; trivial
  · exact checked6708
theorem derived6708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6708 := by
  apply localUnsat_implies_entails f6708 [c6581, c1609] c6708 unsat6708 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1609 := h 1608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6709 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨4, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1610, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6709 : lratChecker f6709 p6709 = .success := by decide +kernel
theorem unsat6709 : Unsatisfiable (PosFin 65) f6709 := by
  apply lratCheckerSound f6709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6709
  · intro a ha; simp [p6709] at ha; subst a; trivial
  · exact checked6709
theorem derived6709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6709 := by
  apply localUnsat_implies_entails f6709 [c6581, c1610] c6709 unsat6709 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1610 := h 1609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6710 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c1649, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6710 : lratChecker f6710 p6710 = .success := by decide +kernel
theorem unsat6710 : Unsatisfiable (PosFin 65) f6710 := by
  apply lratCheckerSound f6710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6710
  · intro a ha; simp [p6710] at ha; subst a; trivial
  · exact checked6710
theorem derived6710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6710 := by
  apply localUnsat_implies_entails f6710 [c6581, c1649] c6710 unsat6710 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c1649 := h 1648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6711 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨50, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2346, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6711 : lratChecker f6711 p6711 = .success := by decide +kernel
theorem unsat6711 : Unsatisfiable (PosFin 65) f6711 := by
  apply lratCheckerSound f6711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6711
  · intro a ha; simp [p6711] at ha; subst a; trivial
  · exact checked6711
theorem derived6711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6711 := by
  apply localUnsat_implies_entails f6711 [c6581, c2346] c6711 unsat6711 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2346 := h 2345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6712 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2466, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6712 : lratChecker f6712 p6712 = .success := by decide +kernel
theorem unsat6712 : Unsatisfiable (PosFin 65) f6712 := by
  apply lratCheckerSound f6712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6712
  · intro a ha; simp [p6712] at ha; subst a; trivial
  · exact checked6712
theorem derived6712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6712 := by
  apply localUnsat_implies_entails f6712 [c6581, c2466] c6712 unsat6712 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2466 := h 2465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6713 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2714, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6713 : lratChecker f6713 p6713 = .success := by decide +kernel
theorem unsat6713 : Unsatisfiable (PosFin 65) f6713 := by
  apply lratCheckerSound f6713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6713
  · intro a ha; simp [p6713] at ha; subst a; trivial
  · exact checked6713
theorem derived6713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6713 := by
  apply localUnsat_implies_entails f6713 [c6581, c2714] c6713 unsat6713 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2714 := h 2713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6714 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2727, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6714 : lratChecker f6714 p6714 = .success := by decide +kernel
theorem unsat6714 : Unsatisfiable (PosFin 65) f6714 := by
  apply lratCheckerSound f6714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6714
  · intro a ha; simp [p6714] at ha; subst a; trivial
  · exact checked6714
theorem derived6714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6714 := by
  apply localUnsat_implies_entails f6714 [c6581, c2727] c6714 unsat6714 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2727 := h 2726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6715 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2741, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6715 : lratChecker f6715 p6715 = .success := by decide +kernel
theorem unsat6715 : Unsatisfiable (PosFin 65) f6715 := by
  apply lratCheckerSound f6715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6715
  · intro a ha; simp [p6715] at ha; subst a; trivial
  · exact checked6715
theorem derived6715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6715 := by
  apply localUnsat_implies_entails f6715 [c6581, c2741] c6715 unsat6715 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2741 := h 2740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6716 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨37, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2745, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6716 : lratChecker f6716 p6716 = .success := by decide +kernel
theorem unsat6716 : Unsatisfiable (PosFin 65) f6716 := by
  apply lratCheckerSound f6716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6716
  · intro a ha; simp [p6716] at ha; subst a; trivial
  · exact checked6716
theorem derived6716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6716 := by
  apply localUnsat_implies_entails f6716 [c6581, c2745] c6716 unsat6716 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2745 := h 2744 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6717 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨39, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2766, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6717 : lratChecker f6717 p6717 = .success := by decide +kernel
theorem unsat6717 : Unsatisfiable (PosFin 65) f6717 := by
  apply lratCheckerSound f6717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6717
  · intro a ha; simp [p6717] at ha; subst a; trivial
  · exact checked6717
theorem derived6717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6717 := by
  apply localUnsat_implies_entails f6717 [c6581, c2766] c6717 unsat6717 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2766 := h 2765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6718 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2768, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6718 : lratChecker f6718 p6718 = .success := by decide +kernel
theorem unsat6718 : Unsatisfiable (PosFin 65) f6718 := by
  apply lratCheckerSound f6718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6718
  · intro a ha; simp [p6718] at ha; subst a; trivial
  · exact checked6718
theorem derived6718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6718 := by
  apply localUnsat_implies_entails f6718 [c6581, c2768] c6718 unsat6718 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2768 := h 2767 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6719 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2792, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6719 : lratChecker f6719 p6719 = .success := by decide +kernel
theorem unsat6719 : Unsatisfiable (PosFin 65) f6719 := by
  apply lratCheckerSound f6719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6719
  · intro a ha; simp [p6719] at ha; subst a; trivial
  · exact checked6719
theorem derived6719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6719 := by
  apply localUnsat_implies_entails f6719 [c6581, c2792] c6719 unsat6719 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2792 := h 2791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6720 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2801, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6720 : lratChecker f6720 p6720 = .success := by decide +kernel
theorem unsat6720 : Unsatisfiable (PosFin 65) f6720 := by
  apply lratCheckerSound f6720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6720
  · intro a ha; simp [p6720] at ha; subst a; trivial
  · exact checked6720
theorem derived6720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6720 := by
  apply localUnsat_implies_entails f6720 [c6581, c2801] c6720 unsat6720 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2801 := h 2800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6721 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2819, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6721 : lratChecker f6721 p6721 = .success := by decide +kernel
theorem unsat6721 : Unsatisfiable (PosFin 65) f6721 := by
  apply lratCheckerSound f6721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6721
  · intro a ha; simp [p6721] at ha; subst a; trivial
  · exact checked6721
theorem derived6721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6721 := by
  apply localUnsat_implies_entails f6721 [c6581, c2819] c6721 unsat6721 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2819 := h 2818 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6722 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2909, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6722 : lratChecker f6722 p6722 = .success := by decide +kernel
theorem unsat6722 : Unsatisfiable (PosFin 65) f6722 := by
  apply lratCheckerSound f6722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6722
  · intro a ha; simp [p6722] at ha; subst a; trivial
  · exact checked6722
theorem derived6722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6722 := by
  apply localUnsat_implies_entails f6722 [c6581, c2909] c6722 unsat6722 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2909 := h 2908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6723 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2910, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6723 : lratChecker f6723 p6723 = .success := by decide +kernel
theorem unsat6723 : Unsatisfiable (PosFin 65) f6723 := by
  apply lratCheckerSound f6723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6723
  · intro a ha; simp [p6723] at ha; subst a; trivial
  · exact checked6723
theorem derived6723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6723 := by
  apply localUnsat_implies_entails f6723 [c6581, c2910] c6723 unsat6723 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2910 := h 2909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6724 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2923, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6724 : lratChecker f6724 p6724 = .success := by decide +kernel
theorem unsat6724 : Unsatisfiable (PosFin 65) f6724 := by
  apply lratCheckerSound f6724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6724
  · intro a ha; simp [p6724] at ha; subst a; trivial
  · exact checked6724
theorem derived6724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6724 := by
  apply localUnsat_implies_entails f6724 [c6581, c2923] c6724 unsat6724 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2923 := h 2922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6725 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨54, by decide⟩, true), (⟨31, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2927, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6725 : lratChecker f6725 p6725 = .success := by decide +kernel
theorem unsat6725 : Unsatisfiable (PosFin 65) f6725 := by
  apply lratCheckerSound f6725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6725
  · intro a ha; simp [p6725] at ha; subst a; trivial
  · exact checked6725
theorem derived6725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6725 := by
  apply localUnsat_implies_entails f6725 [c6581, c2927] c6725 unsat6725 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2927 := h 2926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6726 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨50, by decide⟩, true), (⟨29, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2935, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6726 : lratChecker f6726 p6726 = .success := by decide +kernel
theorem unsat6726 : Unsatisfiable (PosFin 65) f6726 := by
  apply lratCheckerSound f6726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6726
  · intro a ha; simp [p6726] at ha; subst a; trivial
  · exact checked6726
theorem derived6726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6726 := by
  apply localUnsat_implies_entails f6726 [c6581, c2935] c6726 unsat6726 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2935 := h 2934 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6727 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨57, by decide⟩, true), (⟨29, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2937, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6727 : lratChecker f6727 p6727 = .success := by decide +kernel
theorem unsat6727 : Unsatisfiable (PosFin 65) f6727 := by
  apply lratCheckerSound f6727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6727
  · intro a ha; simp [p6727] at ha; subst a; trivial
  · exact checked6727
theorem derived6727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6727 := by
  apply localUnsat_implies_entails f6727 [c6581, c2937] c6727 unsat6727 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2937 := h 2936 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6728 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2961, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6728 : lratChecker f6728 p6728 = .success := by decide +kernel
theorem unsat6728 : Unsatisfiable (PosFin 65) f6728 := by
  apply lratCheckerSound f6728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6728
  · intro a ha; simp [p6728] at ha; subst a; trivial
  · exact checked6728
theorem derived6728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6728 := by
  apply localUnsat_implies_entails f6728 [c6581, c2961] c6728 unsat6728 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2961 := h 2960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6729 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2964, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p6729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6729 : lratChecker f6729 p6729 = .success := by decide +kernel
theorem unsat6729 : Unsatisfiable (PosFin 65) f6729 := by
  apply lratCheckerSound f6729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6729
  · intro a ha; simp [p6729] at ha; subst a; trivial
  · exact checked6729
theorem derived6729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6729 := by
  apply localUnsat_implies_entails f6729 [c6581, c2964] c6729 unsat6729 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2964 := h 2963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6730 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨31, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2965, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6730 : lratChecker f6730 p6730 = .success := by decide +kernel
theorem unsat6730 : Unsatisfiable (PosFin 65) f6730 := by
  apply lratCheckerSound f6730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6730
  · intro a ha; simp [p6730] at ha; subst a; trivial
  · exact checked6730
theorem derived6730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6730 := by
  apply localUnsat_implies_entails f6730 [c6581, c2965] c6730 unsat6730 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2965 := h 2964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6731 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨31, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2967, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6731 : lratChecker f6731 p6731 = .success := by decide +kernel
theorem unsat6731 : Unsatisfiable (PosFin 65) f6731 := by
  apply lratCheckerSound f6731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6731
  · intro a ha; simp [p6731] at ha; subst a; trivial
  · exact checked6731
theorem derived6731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6731 := by
  apply localUnsat_implies_entails f6731 [c6581, c2967] c6731 unsat6731 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2967 := h 2966 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6732 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨60, by decide⟩, true), (⟨31, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2970, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6732 : lratChecker f6732 p6732 = .success := by decide +kernel
theorem unsat6732 : Unsatisfiable (PosFin 65) f6732 := by
  apply lratCheckerSound f6732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6732
  · intro a ha; simp [p6732] at ha; subst a; trivial
  · exact checked6732
theorem derived6732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6732 := by
  apply localUnsat_implies_entails f6732 [c6581, c2970] c6732 unsat6732 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2970 := h 2969 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6733 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2983, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6733 : lratChecker f6733 p6733 = .success := by decide +kernel
theorem unsat6733 : Unsatisfiable (PosFin 65) f6733 := by
  apply lratCheckerSound f6733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6733
  · intro a ha; simp [p6733] at ha; subst a; trivial
  · exact checked6733
theorem derived6733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6733 := by
  apply localUnsat_implies_entails f6733 [c6581, c2983] c6733 unsat6733 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2983 := h 2982 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6734 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c2993, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6734 : lratChecker f6734 p6734 = .success := by decide +kernel
theorem unsat6734 : Unsatisfiable (PosFin 65) f6734 := by
  apply lratCheckerSound f6734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6734
  · intro a ha; simp [p6734] at ha; subst a; trivial
  · exact checked6734
theorem derived6734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6734 := by
  apply localUnsat_implies_entails f6734 [c6581, c2993] c6734 unsat6734 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c2993 := h 2992 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6735 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3000, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6735 : lratChecker f6735 p6735 = .success := by decide +kernel
theorem unsat6735 : Unsatisfiable (PosFin 65) f6735 := by
  apply lratCheckerSound f6735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6735
  · intro a ha; simp [p6735] at ha; subst a; trivial
  · exact checked6735
theorem derived6735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6735 := by
  apply localUnsat_implies_entails f6735 [c6581, c3000] c6735 unsat6735 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3000 := h 2999 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6736 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3001, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6736 : lratChecker f6736 p6736 = .success := by decide +kernel
theorem unsat6736 : Unsatisfiable (PosFin 65) f6736 := by
  apply lratCheckerSound f6736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6736
  · intro a ha; simp [p6736] at ha; subst a; trivial
  · exact checked6736
theorem derived6736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6736 := by
  apply localUnsat_implies_entails f6736 [c6581, c3001] c6736 unsat6736 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3001 := h 3000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6737 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨54, by decide⟩, true), (⟨31, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3016, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6737 : lratChecker f6737 p6737 = .success := by decide +kernel
theorem unsat6737 : Unsatisfiable (PosFin 65) f6737 := by
  apply lratCheckerSound f6737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6737
  · intro a ha; simp [p6737] at ha; subst a; trivial
  · exact checked6737
theorem derived6737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6737 := by
  apply localUnsat_implies_entails f6737 [c6581, c3016] c6737 unsat6737 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3016 := h 3015 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6738 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨56, by decide⟩, true), (⟨31, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3018, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6738 : lratChecker f6738 p6738 = .success := by decide +kernel
theorem unsat6738 : Unsatisfiable (PosFin 65) f6738 := by
  apply lratCheckerSound f6738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6738
  · intro a ha; simp [p6738] at ha; subst a; trivial
  · exact checked6738
theorem derived6738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6738 := by
  apply localUnsat_implies_entails f6738 [c6581, c3018] c6738 unsat6738 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3018 := h 3017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6739 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3032, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6739 : lratChecker f6739 p6739 = .success := by decide +kernel
theorem unsat6739 : Unsatisfiable (PosFin 65) f6739 := by
  apply lratCheckerSound f6739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6739
  · intro a ha; simp [p6739] at ha; subst a; trivial
  · exact checked6739
theorem derived6739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6739 := by
  apply localUnsat_implies_entails f6739 [c6581, c3032] c6739 unsat6739 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3032 := h 3031 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6740 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3033, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6740 : lratChecker f6740 p6740 = .success := by decide +kernel
theorem unsat6740 : Unsatisfiable (PosFin 65) f6740 := by
  apply lratCheckerSound f6740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6740
  · intro a ha; simp [p6740] at ha; subst a; trivial
  · exact checked6740
theorem derived6740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6740 := by
  apply localUnsat_implies_entails f6740 [c6581, c3033] c6740 unsat6740 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3033 := h 3032 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6741 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3034, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6741 : lratChecker f6741 p6741 = .success := by decide +kernel
theorem unsat6741 : Unsatisfiable (PosFin 65) f6741 := by
  apply lratCheckerSound f6741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6741
  · intro a ha; simp [p6741] at ha; subst a; trivial
  · exact checked6741
theorem derived6741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6741 := by
  apply localUnsat_implies_entails f6741 [c6581, c3034] c6741 unsat6741 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3034 := h 3033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6742 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3041, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6742 : lratChecker f6742 p6742 = .success := by decide +kernel
theorem unsat6742 : Unsatisfiable (PosFin 65) f6742 := by
  apply lratCheckerSound f6742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6742
  · intro a ha; simp [p6742] at ha; subst a; trivial
  · exact checked6742
theorem derived6742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6742 := by
  apply localUnsat_implies_entails f6742 [c6581, c3041] c6742 unsat6742 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3041 := h 3040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6743 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, true), (⟨19, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3044, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6743 : lratChecker f6743 p6743 = .success := by decide +kernel
theorem unsat6743 : Unsatisfiable (PosFin 65) f6743 := by
  apply lratCheckerSound f6743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6743
  · intro a ha; simp [p6743] at ha; subst a; trivial
  · exact checked6743
theorem derived6743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6743 := by
  apply localUnsat_implies_entails f6743 [c6581, c3044] c6743 unsat6743 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3044 := h 3043 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6744 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3045, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6744 : lratChecker f6744 p6744 = .success := by decide +kernel
theorem unsat6744 : Unsatisfiable (PosFin 65) f6744 := by
  apply lratCheckerSound f6744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6744
  · intro a ha; simp [p6744] at ha; subst a; trivial
  · exact checked6744
theorem derived6744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6744 := by
  apply localUnsat_implies_entails f6744 [c6581, c3045] c6744 unsat6744 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3045 := h 3044 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6745 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3065, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6745 : lratChecker f6745 p6745 = .success := by decide +kernel
theorem unsat6745 : Unsatisfiable (PosFin 65) f6745 := by
  apply lratCheckerSound f6745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6745
  · intro a ha; simp [p6745] at ha; subst a; trivial
  · exact checked6745
theorem derived6745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6745 := by
  apply localUnsat_implies_entails f6745 [c6581, c3065] c6745 unsat6745 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3065 := h 3064 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6746 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3078, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6746 : lratChecker f6746 p6746 = .success := by decide +kernel
theorem unsat6746 : Unsatisfiable (PosFin 65) f6746 := by
  apply lratCheckerSound f6746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6746
  · intro a ha; simp [p6746] at ha; subst a; trivial
  · exact checked6746
theorem derived6746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6746 := by
  apply localUnsat_implies_entails f6746 [c6581, c3078] c6746 unsat6746 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3078 := h 3077 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6747 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3108, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6747 : lratChecker f6747 p6747 = .success := by decide +kernel
theorem unsat6747 : Unsatisfiable (PosFin 65) f6747 := by
  apply lratCheckerSound f6747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6747
  · intro a ha; simp [p6747] at ha; subst a; trivial
  · exact checked6747
theorem derived6747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6747 := by
  apply localUnsat_implies_entails f6747 [c6581, c3108] c6747 unsat6747 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3108 := h 3107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6748 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3109, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6748 : lratChecker f6748 p6748 = .success := by decide +kernel
theorem unsat6748 : Unsatisfiable (PosFin 65) f6748 := by
  apply lratCheckerSound f6748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6748
  · intro a ha; simp [p6748] at ha; subst a; trivial
  · exact checked6748
theorem derived6748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6748 := by
  apply localUnsat_implies_entails f6748 [c6581, c3109] c6748 unsat6748 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3109 := h 3108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6749 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨60, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3119, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6749 : lratChecker f6749 p6749 = .success := by decide +kernel
theorem unsat6749 : Unsatisfiable (PosFin 65) f6749 := by
  apply lratCheckerSound f6749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6749
  · intro a ha; simp [p6749] at ha; subst a; trivial
  · exact checked6749
theorem derived6749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6749 := by
  apply localUnsat_implies_entails f6749 [c6581, c3119] c6749 unsat6749 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3119 := h 3118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6750 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3126, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6750 : lratChecker f6750 p6750 = .success := by decide +kernel
theorem unsat6750 : Unsatisfiable (PosFin 65) f6750 := by
  apply lratCheckerSound f6750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6750
  · intro a ha; simp [p6750] at ha; subst a; trivial
  · exact checked6750
theorem derived6750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6750 := by
  apply localUnsat_implies_entails f6750 [c6581, c3126] c6750 unsat6750 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3126 := h 3125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6751 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨50, by decide⟩, true), (⟨21, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3140, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6751 : lratChecker f6751 p6751 = .success := by decide +kernel
theorem unsat6751 : Unsatisfiable (PosFin 65) f6751 := by
  apply lratCheckerSound f6751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6751
  · intro a ha; simp [p6751] at ha; subst a; trivial
  · exact checked6751
theorem derived6751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6751 := by
  apply localUnsat_implies_entails f6751 [c6581, c3140] c6751 unsat6751 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3140 := h 3139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6752 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, true), (⟨21, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3141, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6752 : lratChecker f6752 p6752 = .success := by decide +kernel
theorem unsat6752 : Unsatisfiable (PosFin 65) f6752 := by
  apply lratCheckerSound f6752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6752
  · intro a ha; simp [p6752] at ha; subst a; trivial
  · exact checked6752
theorem derived6752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6752 := by
  apply localUnsat_implies_entails f6752 [c6581, c3141] c6752 unsat6752 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3141 := h 3140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6753 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨22, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3145, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6753 : lratChecker f6753 p6753 = .success := by decide +kernel
theorem unsat6753 : Unsatisfiable (PosFin 65) f6753 := by
  apply lratCheckerSound f6753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6753
  · intro a ha; simp [p6753] at ha; subst a; trivial
  · exact checked6753
theorem derived6753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6753 := by
  apply localUnsat_implies_entails f6753 [c6581, c3145] c6753 unsat6753 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3145 := h 3144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6754 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3169, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6754 : lratChecker f6754 p6754 = .success := by decide +kernel
theorem unsat6754 : Unsatisfiable (PosFin 65) f6754 := by
  apply lratCheckerSound f6754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6754
  · intro a ha; simp [p6754] at ha; subst a; trivial
  · exact checked6754
theorem derived6754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6754 := by
  apply localUnsat_implies_entails f6754 [c6581, c3169] c6754 unsat6754 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3169 := h 3168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6755 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3170, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6755 : lratChecker f6755 p6755 = .success := by decide +kernel
theorem unsat6755 : Unsatisfiable (PosFin 65) f6755 := by
  apply lratCheckerSound f6755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6755
  · intro a ha; simp [p6755] at ha; subst a; trivial
  · exact checked6755
theorem derived6755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6755 := by
  apply localUnsat_implies_entails f6755 [c6581, c3170] c6755 unsat6755 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3170 := h 3169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6756 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨60, by decide⟩, true), (⟨21, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3195, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6756 : lratChecker f6756 p6756 = .success := by decide +kernel
theorem unsat6756 : Unsatisfiable (PosFin 65) f6756 := by
  apply lratCheckerSound f6756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6756
  · intro a ha; simp [p6756] at ha; subst a; trivial
  · exact checked6756
theorem derived6756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6756 := by
  apply localUnsat_implies_entails f6756 [c6581, c3195] c6756 unsat6756 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3195 := h 3194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6757 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3201, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p6757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6757 : lratChecker f6757 p6757 = .success := by decide +kernel
theorem unsat6757 : Unsatisfiable (PosFin 65) f6757 := by
  apply lratCheckerSound f6757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6757
  · intro a ha; simp [p6757] at ha; subst a; trivial
  · exact checked6757
theorem derived6757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6757 := by
  apply localUnsat_implies_entails f6757 [c6581, c3201] c6757 unsat6757 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3201 := h 3200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6758 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨23, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3219, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6758 : lratChecker f6758 p6758 = .success := by decide +kernel
theorem unsat6758 : Unsatisfiable (PosFin 65) f6758 := by
  apply lratCheckerSound f6758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6758
  · intro a ha; simp [p6758] at ha; subst a; trivial
  · exact checked6758
theorem derived6758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6758 := by
  apply localUnsat_implies_entails f6758 [c6581, c3219] c6758 unsat6758 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3219 := h 3218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6759 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨60, by decide⟩, true), (⟨20, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3236, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6759 : lratChecker f6759 p6759 = .success := by decide +kernel
theorem unsat6759 : Unsatisfiable (PosFin 65) f6759 := by
  apply lratCheckerSound f6759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6759
  · intro a ha; simp [p6759] at ha; subst a; trivial
  · exact checked6759
theorem derived6759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6759 := by
  apply localUnsat_implies_entails f6759 [c6581, c3236] c6759 unsat6759 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3236 := h 3235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6760 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨49, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3249, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6760 : lratChecker f6760 p6760 = .success := by decide +kernel
theorem unsat6760 : Unsatisfiable (PosFin 65) f6760 := by
  apply lratCheckerSound f6760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6760
  · intro a ha; simp [p6760] at ha; subst a; trivial
  · exact checked6760
theorem derived6760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6760 := by
  apply localUnsat_implies_entails f6760 [c6581, c3249] c6760 unsat6760 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3249 := h 3248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6761 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨54, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3250, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p6761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6761 : lratChecker f6761 p6761 = .success := by decide +kernel
theorem unsat6761 : Unsatisfiable (PosFin 65) f6761 := by
  apply lratCheckerSound f6761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6761
  · intro a ha; simp [p6761] at ha; subst a; trivial
  · exact checked6761
theorem derived6761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6761 := by
  apply localUnsat_implies_entails f6761 [c6581, c3250] c6761 unsat6761 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3250 := h 3249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6762 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3256, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6762 : lratChecker f6762 p6762 = .success := by decide +kernel
theorem unsat6762 : Unsatisfiable (PosFin 65) f6762 := by
  apply lratCheckerSound f6762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6762
  · intro a ha; simp [p6762] at ha; subst a; trivial
  · exact checked6762
theorem derived6762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6762 := by
  apply localUnsat_implies_entails f6762 [c6581, c3256] c6762 unsat6762 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3256 := h 3255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6763 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3261, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6763 : lratChecker f6763 p6763 = .success := by decide +kernel
theorem unsat6763 : Unsatisfiable (PosFin 65) f6763 := by
  apply lratCheckerSound f6763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6763
  · intro a ha; simp [p6763] at ha; subst a; trivial
  · exact checked6763
theorem derived6763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6763 := by
  apply localUnsat_implies_entails f6763 [c6581, c3261] c6763 unsat6763 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3261 := h 3260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6764 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3279, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6764 : lratChecker f6764 p6764 = .success := by decide +kernel
theorem unsat6764 : Unsatisfiable (PosFin 65) f6764 := by
  apply lratCheckerSound f6764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6764
  · intro a ha; simp [p6764] at ha; subst a; trivial
  · exact checked6764
theorem derived6764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6764 := by
  apply localUnsat_implies_entails f6764 [c6581, c3279] c6764 unsat6764 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3279 := h 3278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6765 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3282, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6765 : lratChecker f6765 p6765 = .success := by decide +kernel
theorem unsat6765 : Unsatisfiable (PosFin 65) f6765 := by
  apply lratCheckerSound f6765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6765
  · intro a ha; simp [p6765] at ha; subst a; trivial
  · exact checked6765
theorem derived6765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6765 := by
  apply localUnsat_implies_entails f6765 [c6581, c3282] c6765 unsat6765 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3282 := h 3281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6766 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3324, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6766 : lratChecker f6766 p6766 = .success := by decide +kernel
theorem unsat6766 : Unsatisfiable (PosFin 65) f6766 := by
  apply lratCheckerSound f6766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6766
  · intro a ha; simp [p6766] at ha; subst a; trivial
  · exact checked6766
theorem derived6766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6766 := by
  apply localUnsat_implies_entails f6766 [c6581, c3324] c6766 unsat6766 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3324 := h 3323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6767 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨49, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3341, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6767 : lratChecker f6767 p6767 = .success := by decide +kernel
theorem unsat6767 : Unsatisfiable (PosFin 65) f6767 := by
  apply lratCheckerSound f6767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6767
  · intro a ha; simp [p6767] at ha; subst a; trivial
  · exact checked6767
theorem derived6767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6767 := by
  apply localUnsat_implies_entails f6767 [c6581, c3341] c6767 unsat6767 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3341 := h 3340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6768 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨49, by decide⟩, true), (⟨27, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3370, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6768 : lratChecker f6768 p6768 = .success := by decide +kernel
theorem unsat6768 : Unsatisfiable (PosFin 65) f6768 := by
  apply lratCheckerSound f6768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6768
  · intro a ha; simp [p6768] at ha; subst a; trivial
  · exact checked6768
theorem derived6768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6768 := by
  apply localUnsat_implies_entails f6768 [c6581, c3370] c6768 unsat6768 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3370 := h 3369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6769 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨57, by decide⟩, true), (⟨27, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3372, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p6769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6769 : lratChecker f6769 p6769 = .success := by decide +kernel
theorem unsat6769 : Unsatisfiable (PosFin 65) f6769 := by
  apply lratCheckerSound f6769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6769
  · intro a ha; simp [p6769] at ha; subst a; trivial
  · exact checked6769
theorem derived6769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6769 := by
  apply localUnsat_implies_entails f6769 [c6581, c3372] c6769 unsat6769 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3372 := h 3371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6770 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, true), (⟨27, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3375, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p6770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6770 : lratChecker f6770 p6770 = .success := by decide +kernel
theorem unsat6770 : Unsatisfiable (PosFin 65) f6770 := by
  apply lratCheckerSound f6770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6770
  · intro a ha; simp [p6770] at ha; subst a; trivial
  · exact checked6770
theorem derived6770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6770 := by
  apply localUnsat_implies_entails f6770 [c6581, c3375] c6770 unsat6770 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3375 := h 3374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6771 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3394, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6771 : lratChecker f6771 p6771 = .success := by decide +kernel
theorem unsat6771 : Unsatisfiable (PosFin 65) f6771 := by
  apply lratCheckerSound f6771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6771
  · intro a ha; simp [p6771] at ha; subst a; trivial
  · exact checked6771
theorem derived6771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6771 := by
  apply localUnsat_implies_entails f6771 [c6581, c3394] c6771 unsat6771 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3394 := h 3393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6772 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3395, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p6772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6772 : lratChecker f6772 p6772 = .success := by decide +kernel
theorem unsat6772 : Unsatisfiable (PosFin 65) f6772 := by
  apply lratCheckerSound f6772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6772
  · intro a ha; simp [p6772] at ha; subst a; trivial
  · exact checked6772
theorem derived6772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6772 := by
  apply localUnsat_implies_entails f6772 [c6581, c3395] c6772 unsat6772 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3395 := h 3394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6773 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨54, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3397, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6773 : lratChecker f6773 p6773 = .success := by decide +kernel
theorem unsat6773 : Unsatisfiable (PosFin 65) f6773 := by
  apply lratCheckerSound f6773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6773
  · intro a ha; simp [p6773] at ha; subst a; trivial
  · exact checked6773
theorem derived6773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6773 := by
  apply localUnsat_implies_entails f6773 [c6581, c3397] c6773 unsat6773 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3397 := h 3396 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6774 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨26, by decide⟩, true), (⟨49, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3407, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6774 : lratChecker f6774 p6774 = .success := by decide +kernel
theorem unsat6774 : Unsatisfiable (PosFin 65) f6774 := by
  apply lratCheckerSound f6774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6774
  · intro a ha; simp [p6774] at ha; subst a; trivial
  · exact checked6774
theorem derived6774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6774 := by
  apply localUnsat_implies_entails f6774 [c6581, c3407] c6774 unsat6774 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3407 := h 3406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6775 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3408, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p6775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6775 : lratChecker f6775 p6775 = .success := by decide +kernel
theorem unsat6775 : Unsatisfiable (PosFin 65) f6775 := by
  apply lratCheckerSound f6775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6775
  · intro a ha; simp [p6775] at ha; subst a; trivial
  · exact checked6775
theorem derived6775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6775 := by
  apply localUnsat_implies_entails f6775 [c6581, c3408] c6775 unsat6775 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3408 := h 3407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6776 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, true), (⟨29, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3412, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6776 : lratChecker f6776 p6776 = .success := by decide +kernel
theorem unsat6776 : Unsatisfiable (PosFin 65) f6776 := by
  apply lratCheckerSound f6776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6776
  · intro a ha; simp [p6776] at ha; subst a; trivial
  · exact checked6776
theorem derived6776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6776 := by
  apply localUnsat_implies_entails f6776 [c6581, c3412] c6776 unsat6776 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3412 := h 3411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6777 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨56, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3414, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6777 : lratChecker f6777 p6777 = .success := by decide +kernel
theorem unsat6777 : Unsatisfiable (PosFin 65) f6777 := by
  apply lratCheckerSound f6777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6777
  · intro a ha; simp [p6777] at ha; subst a; trivial
  · exact checked6777
theorem derived6777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6777 := by
  apply localUnsat_implies_entails f6777 [c6581, c3414] c6777 unsat6777 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3414 := h 3413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6778 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨57, by decide⟩, true), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f6778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3495, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p6778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6778 : lratChecker f6778 p6778 = .success := by decide +kernel
theorem unsat6778 : Unsatisfiable (PosFin 65) f6778 := by
  apply lratCheckerSound f6778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6778
  · intro a ha; simp [p6778] at ha; subst a; trivial
  · exact checked6778
theorem derived6778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6778 := by
  apply localUnsat_implies_entails f6778 [c6581, c3495] c6778 unsat6778 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3495 := h 3494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6779 : DefaultClause 65 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3510, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p6779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6779 : lratChecker f6779 p6779 = .success := by decide +kernel
theorem unsat6779 : Unsatisfiable (PosFin 65) f6779 := by
  apply lratCheckerSound f6779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6779
  · intro a ha; simp [p6779] at ha; subst a; trivial
  · exact checked6779
theorem derived6779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6779 := by
  apply localUnsat_implies_entails f6779 [c6581, c3510] c6779 unsat6779 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3510 := h 3509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c6780 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f6780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6581, some c3517, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p6780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked6780 : lratChecker f6780 p6780 = .success := by decide +kernel
theorem unsat6780 : Unsatisfiable (PosFin 65) f6780 := by
  apply lratCheckerSound f6780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p6780
  · intro a ha; simp [p6780] at ha; subst a; trivial
  · exact checked6780
theorem derived6780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c6780 := by
  apply localUnsat_implies_entails f6780 [c6581, c3517] c6780 unsat6780 (by rfl) a
  have h0 : Entails.eval a c6581 := derived6581 a h
  have h1 : Entails.eval a c3517 := h 3516 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived6780

end CochromaticTwenty.Certificates.FixedCore1
