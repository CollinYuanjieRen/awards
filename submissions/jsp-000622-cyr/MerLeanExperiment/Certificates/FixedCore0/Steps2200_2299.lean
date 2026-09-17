import MerLeanExperiment.Certificates.FixedCore0.Steps2100_2199

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9751 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9749, some c3595, some c3584, some c8001, some c9750, some c3053, some c3828, some c4259, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9751 : lratChecker f9751 p9751 = .success := by decide +kernel
theorem unsat9751 : Unsatisfiable (PosFin 65) f9751 := by
  apply lratCheckerSound f9751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9751
  · intro a ha; simp [p9751] at ha; subst a; trivial
  · exact checked9751
theorem derived9751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9751 := by
  apply localUnsat_implies_entails f9751 [c9749, c3595, c3584, c8001, c9750, c3053, c3828, c4259] c9751 unsat9751 (by rfl) a
  have h0 : Entails.eval a c9749 := derived9749 a h
  have h1 : Entails.eval a c3595 := h 3594 (by decide)
  have h2 : Entails.eval a c3584 := h 3583 (by decide)
  have h3 : Entails.eval a c8001 := derived8001 a h
  have h4 : Entails.eval a c9750 := derived9750 a h
  have h5 : Entails.eval a c3053 := h 3052 (by decide)
  have h6 : Entails.eval a c3828 := h 3827 (by decide)
  have h7 : Entails.eval a c4259 := h 4258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9752 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1951, some c2731, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9752 : lratChecker f9752 p9752 = .success := by decide +kernel
theorem unsat9752 : Unsatisfiable (PosFin 65) f9752 := by
  apply lratCheckerSound f9752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9752
  · intro a ha; simp [p9752] at ha; subst a; trivial
  · exact checked9752
theorem derived9752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9752 := by
  apply localUnsat_implies_entails f9752 [c9748, c1951, c2731] c9752 unsat9752 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1951 := h 1950 (by decide)
  have h2 : Entails.eval a c2731 := h 2730 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9753 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9752, some c1956, some c2754, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9753 : lratChecker f9753 p9753 = .success := by decide +kernel
theorem unsat9753 : Unsatisfiable (PosFin 65) f9753 := by
  apply lratCheckerSound f9753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9753
  · intro a ha; simp [p9753] at ha; subst a; trivial
  · exact checked9753
theorem derived9753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9753 := by
  apply localUnsat_implies_entails f9753 [c9748, c9752, c1956, c2754] c9753 unsat9753 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9752 := derived9752 a h
  have h2 : Entails.eval a c1956 := h 1955 (by decide)
  have h3 : Entails.eval a c2754 := h 2753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9754 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨52, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9751, some c9753, some c9750, some c2731, some c9352, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9754 : lratChecker f9754 p9754 = .success := by decide +kernel
theorem unsat9754 : Unsatisfiable (PosFin 65) f9754 := by
  apply lratCheckerSound f9754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9754
  · intro a ha; simp [p9754] at ha; subst a; trivial
  · exact checked9754
theorem derived9754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9754 := by
  apply localUnsat_implies_entails f9754 [c9751, c9753, c9750, c2731, c9352] c9754 unsat9754 (by rfl) a
  have h0 : Entails.eval a c9751 := derived9751 a h
  have h1 : Entails.eval a c9753 := derived9753 a h
  have h2 : Entails.eval a c9750 := derived9750 a h
  have h3 : Entails.eval a c2731 := h 2730 (by decide)
  have h4 : Entails.eval a c9352 := derived9352 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9755 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3591, some c4618, some c4553, some c2743, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9755 : lratChecker f9755 p9755 = .success := by decide +kernel
theorem unsat9755 : Unsatisfiable (PosFin 65) f9755 := by
  apply lratCheckerSound f9755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9755
  · intro a ha; simp [p9755] at ha; subst a; trivial
  · exact checked9755
theorem derived9755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9755 := by
  apply localUnsat_implies_entails f9755 [c3591, c4618, c4553, c2743] c9755 unsat9755 (by rfl) a
  have h0 : Entails.eval a c3591 := h 3590 (by decide)
  have h1 : Entails.eval a c4618 := h 4617 (by decide)
  have h2 : Entails.eval a c4553 := h 4552 (by decide)
  have h3 : Entails.eval a c2743 := h 2742 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9756 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3405, some c2059, some c2352, some c1560, some c4078, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9756 : lratChecker f9756 p9756 = .success := by decide +kernel
theorem unsat9756 : Unsatisfiable (PosFin 65) f9756 := by
  apply lratCheckerSound f9756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9756
  · intro a ha; simp [p9756] at ha; subst a; trivial
  · exact checked9756
theorem derived9756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9756 := by
  apply localUnsat_implies_entails f9756 [c9748, c3405, c2059, c2352, c1560, c4078] c9756 unsat9756 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3405 := h 3404 (by decide)
  have h2 : Entails.eval a c2059 := h 2058 (by decide)
  have h3 : Entails.eval a c2352 := h 2351 (by decide)
  have h4 : Entails.eval a c1560 := h 1559 (by decide)
  have h5 : Entails.eval a c4078 := h 4077 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9757 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9754, some c3597, some c3048, some c1527, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9757 : lratChecker f9757 p9757 = .success := by decide +kernel
theorem unsat9757 : Unsatisfiable (PosFin 65) f9757 := by
  apply lratCheckerSound f9757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9757
  · intro a ha; simp [p9757] at ha; subst a; trivial
  · exact checked9757
theorem derived9757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9757 := by
  apply localUnsat_implies_entails f9757 [c9748, c9754, c3597, c3048, c1527] c9757 unsat9757 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9754 := derived9754 a h
  have h2 : Entails.eval a c3597 := h 3596 (by decide)
  have h3 : Entails.eval a c3048 := h 3047 (by decide)
  have h4 : Entails.eval a c1527 := h 1526 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9758 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9755, some c9756, some c9757, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9758 : lratChecker f9758 p9758 = .success := by decide +kernel
theorem unsat9758 : Unsatisfiable (PosFin 65) f9758 := by
  apply lratCheckerSound f9758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9758
  · intro a ha; simp [p9758] at ha; subst a; trivial
  · exact checked9758
theorem derived9758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9758 := by
  apply localUnsat_implies_entails f9758 [c9755, c9756, c9757] c9758 unsat9758 (by rfl) a
  have h0 : Entails.eval a c9755 := derived9755 a h
  have h1 : Entails.eval a c9756 := derived9756 a h
  have h2 : Entails.eval a c9757 := derived9757 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9759 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3595, some c3580, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9759 : lratChecker f9759 p9759 = .success := by decide +kernel
theorem unsat9759 : Unsatisfiable (PosFin 65) f9759 := by
  apply lratCheckerSound f9759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9759
  · intro a ha; simp [p9759] at ha; subst a; trivial
  · exact checked9759
theorem derived9759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9759 := by
  apply localUnsat_implies_entails f9759 [c3595, c3580] c9759 unsat9759 (by rfl) a
  have h0 : Entails.eval a c3595 := h 3594 (by decide)
  have h1 : Entails.eval a c3580 := h 3579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9760 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1938, some c2754, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9760 : lratChecker f9760 p9760 = .success := by decide +kernel
theorem unsat9760 : Unsatisfiable (PosFin 65) f9760 := by
  apply lratCheckerSound f9760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9760
  · intro a ha; simp [p9760] at ha; subst a; trivial
  · exact checked9760
theorem derived9760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9760 := by
  apply localUnsat_implies_entails f9760 [c9748, c1938, c2754] c9760 unsat9760 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1938 := h 1937 (by decide)
  have h2 : Entails.eval a c2754 := h 2753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9761 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨7, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2027, some c1960, some c9213, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9761 : lratChecker f9761 p9761 = .success := by decide +kernel
theorem unsat9761 : Unsatisfiable (PosFin 65) f9761 := by
  apply lratCheckerSound f9761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9761
  · intro a ha; simp [p9761] at ha; subst a; trivial
  · exact checked9761
theorem derived9761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9761 := by
  apply localUnsat_implies_entails f9761 [c9748, c2027, c1960, c9213] c9761 unsat9761 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2027 := h 2026 (by decide)
  have h2 : Entails.eval a c1960 := h 1959 (by decide)
  have h3 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9762 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9758, some c9759, some c9761, some c3811, some c4667, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9762 : lratChecker f9762 p9762 = .success := by decide +kernel
theorem unsat9762 : Unsatisfiable (PosFin 65) f9762 := by
  apply lratCheckerSound f9762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9762
  · intro a ha; simp [p9762] at ha; subst a; trivial
  · exact checked9762
theorem derived9762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9762 := by
  apply localUnsat_implies_entails f9762 [c9758, c9759, c9761, c3811, c4667] c9762 unsat9762 (by rfl) a
  have h0 : Entails.eval a c9758 := derived9758 a h
  have h1 : Entails.eval a c9759 := derived9759 a h
  have h2 : Entails.eval a c9761 := derived9761 a h
  have h3 : Entails.eval a c3811 := h 3810 (by decide)
  have h4 : Entails.eval a c4667 := h 4666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9763 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨61, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9749, some c9752, some c9760, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9763 : lratChecker f9763 p9763 = .success := by decide +kernel
theorem unsat9763 : Unsatisfiable (PosFin 65) f9763 := by
  apply lratCheckerSound f9763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9763
  · intro a ha; simp [p9763] at ha; subst a; trivial
  · exact checked9763
theorem derived9763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9763 := by
  apply localUnsat_implies_entails f9763 [c9749, c9752, c9760] c9763 unsat9763 (by rfl) a
  have h0 : Entails.eval a c9749 := derived9749 a h
  have h1 : Entails.eval a c9752 := derived9752 a h
  have h2 : Entails.eval a c9760 := derived9760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9764 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨61, by decide⟩, false), (⟨57, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3595, some c3597, some c3599, some c3598, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9764 : lratChecker f9764 p9764 = .success := by decide +kernel
theorem unsat9764 : Unsatisfiable (PosFin 65) f9764 := by
  apply lratCheckerSound f9764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9764
  · intro a ha; simp [p9764] at ha; subst a; trivial
  · exact checked9764
theorem derived9764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9764 := by
  apply localUnsat_implies_entails f9764 [c3595, c3597, c3599, c3598] c9764 unsat9764 (by rfl) a
  have h0 : Entails.eval a c3595 := h 3594 (by decide)
  have h1 : Entails.eval a c3597 := h 3596 (by decide)
  have h2 : Entails.eval a c3599 := h 3598 (by decide)
  have h3 : Entails.eval a c3598 := h 3597 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9765 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨57, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9764, some c9749, some c9763, some c1999, some c5080, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9765 : lratChecker f9765 p9765 = .success := by decide +kernel
theorem unsat9765 : Unsatisfiable (PosFin 65) f9765 := by
  apply lratCheckerSound f9765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9765
  · intro a ha; simp [p9765] at ha; subst a; trivial
  · exact checked9765
theorem derived9765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9765 := by
  apply localUnsat_implies_entails f9765 [c9748, c9764, c9749, c9763, c1999, c5080] c9765 unsat9765 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9764 := derived9764 a h
  have h2 : Entails.eval a c9749 := derived9749 a h
  have h3 : Entails.eval a c9763 := derived9763 a h
  have h4 : Entails.eval a c1999 := h 1998 (by decide)
  have h5 : Entails.eval a c5080 := h 5079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9766 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4621, some c4611, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9766 : lratChecker f9766 p9766 = .success := by decide +kernel
theorem unsat9766 : Unsatisfiable (PosFin 65) f9766 := by
  apply lratCheckerSound f9766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9766
  · intro a ha; simp [p9766] at ha; subst a; trivial
  · exact checked9766
theorem derived9766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9766 := by
  apply localUnsat_implies_entails f9766 [c4621, c4611] c9766 unsat9766 (by rfl) a
  have h0 : Entails.eval a c4621 := h 4620 (by decide)
  have h1 : Entails.eval a c4611 := h 4610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9767 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9766, some c9760, some c9352, some c4657, some c9213, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9767 : lratChecker f9767 p9767 = .success := by decide +kernel
theorem unsat9767 : Unsatisfiable (PosFin 65) f9767 := by
  apply lratCheckerSound f9767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9767
  · intro a ha; simp [p9767] at ha; subst a; trivial
  · exact checked9767
theorem derived9767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9767 := by
  apply localUnsat_implies_entails f9767 [c9766, c9760, c9352, c4657, c9213] c9767 unsat9767 (by rfl) a
  have h0 : Entails.eval a c9766 := derived9766 a h
  have h1 : Entails.eval a c9760 := derived9760 a h
  have h2 : Entails.eval a c9352 := derived9352 a h
  have h3 : Entails.eval a c4657 := h 4656 (by decide)
  have h4 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9768 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9762, some c9765, some c9755, some c9759, some c9767, some c1999, some c4619, some c5080, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9768 : lratChecker f9768 p9768 = .success := by decide +kernel
theorem unsat9768 : Unsatisfiable (PosFin 65) f9768 := by
  apply lratCheckerSound f9768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9768
  · intro a ha; simp [p9768] at ha; subst a; trivial
  · exact checked9768
theorem derived9768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9768 := by
  apply localUnsat_implies_entails f9768 [c9748, c9762, c9765, c9755, c9759, c9767, c1999, c4619, c5080] c9768 unsat9768 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9762 := derived9762 a h
  have h2 : Entails.eval a c9765 := derived9765 a h
  have h3 : Entails.eval a c9755 := derived9755 a h
  have h4 : Entails.eval a c9759 := derived9759 a h
  have h5 : Entails.eval a c9767 := derived9767 a h
  have h6 : Entails.eval a c1999 := h 1998 (by decide)
  have h7 : Entails.eval a c4619 := h 4618 (by decide)
  have h8 : Entails.eval a c5080 := h 5079 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9769 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3406, some c3037, some c1563, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9769 : lratChecker f9769 p9769 = .success := by decide +kernel
theorem unsat9769 : Unsatisfiable (PosFin 65) f9769 := by
  apply lratCheckerSound f9769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9769
  · intro a ha; simp [p9769] at ha; subst a; trivial
  · exact checked9769
theorem derived9769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9769 := by
  apply localUnsat_implies_entails f9769 [c9748, c3406, c3037, c1563] c9769 unsat9769 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3406 := h 3405 (by decide)
  have h2 : Entails.eval a c3037 := h 3036 (by decide)
  have h3 : Entails.eval a c1563 := h 1562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9770 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨61, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4643, some c4642, some c4638, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9770 : lratChecker f9770 p9770 = .success := by decide +kernel
theorem unsat9770 : Unsatisfiable (PosFin 65) f9770 := by
  apply lratCheckerSound f9770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9770
  · intro a ha; simp [p9770] at ha; subst a; trivial
  · exact checked9770
theorem derived9770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9770 := by
  apply localUnsat_implies_entails f9770 [c4643, c4642, c4638] c9770 unsat9770 (by rfl) a
  have h0 : Entails.eval a c4643 := h 4642 (by decide)
  have h1 : Entails.eval a c4642 := h 4641 (by decide)
  have h2 : Entails.eval a c4638 := h 4637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9771 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1947, some c2742, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9771 : lratChecker f9771 p9771 = .success := by decide +kernel
theorem unsat9771 : Unsatisfiable (PosFin 65) f9771 := by
  apply lratCheckerSound f9771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9771
  · intro a ha; simp [p9771] at ha; subst a; trivial
  · exact checked9771
theorem derived9771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9771 := by
  apply localUnsat_implies_entails f9771 [c9748, c1947, c2742] c9771 unsat9771 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1947 := h 1946 (by decide)
  have h2 : Entails.eval a c2742 := h 2741 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9772 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9352, some c4657, some c9213, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9772 : lratChecker f9772 p9772 = .success := by decide +kernel
theorem unsat9772 : Unsatisfiable (PosFin 65) f9772 := by
  apply lratCheckerSound f9772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9772
  · intro a ha; simp [p9772] at ha; subst a; trivial
  · exact checked9772
theorem derived9772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9772 := by
  apply localUnsat_implies_entails f9772 [c9352, c4657, c9213] c9772 unsat9772 (by rfl) a
  have h0 : Entails.eval a c9352 := derived9352 a h
  have h1 : Entails.eval a c4657 := h 4656 (by decide)
  have h2 : Entails.eval a c9213 := derived9213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9773 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3816, some c4667, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9773 : lratChecker f9773 p9773 = .success := by decide +kernel
theorem unsat9773 : Unsatisfiable (PosFin 65) f9773 := by
  apply lratCheckerSound f9773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9773
  · intro a ha; simp [p9773] at ha; subst a; trivial
  · exact checked9773
theorem derived9773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9773 := by
  apply localUnsat_implies_entails f9773 [c3816, c4667] c9773 unsat9773 (by rfl) a
  have h0 : Entails.eval a c3816 := h 3815 (by decide)
  have h1 : Entails.eval a c4667 := h 4666 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9774 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4631, some c4622, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9774 : lratChecker f9774 p9774 = .success := by decide +kernel
theorem unsat9774 : Unsatisfiable (PosFin 65) f9774 := by
  apply lratCheckerSound f9774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9774
  · intro a ha; simp [p9774] at ha; subst a; trivial
  · exact checked9774
theorem derived9774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9774 := by
  apply localUnsat_implies_entails f9774 [c4631, c4622] c9774 unsat9774 (by rfl) a
  have h0 : Entails.eval a c4631 := h 4630 (by decide)
  have h1 : Entails.eval a c4622 := h 4621 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9775 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨57, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3046, some c1519, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9775 : lratChecker f9775 p9775 = .success := by decide +kernel
theorem unsat9775 : Unsatisfiable (PosFin 65) f9775 := by
  apply lratCheckerSound f9775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9775
  · intro a ha; simp [p9775] at ha; subst a; trivial
  · exact checked9775
theorem derived9775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9775 := by
  apply localUnsat_implies_entails f9775 [c9748, c3046, c1519] c9775 unsat9775 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3046 := h 3045 (by decide)
  have h2 : Entails.eval a c1519 := h 1518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9776 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9769, some c9773, some c9772, some c9775, some c3043, some c1500, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9776 : lratChecker f9776 p9776 = .success := by decide +kernel
theorem unsat9776 : Unsatisfiable (PosFin 65) f9776 := by
  apply lratCheckerSound f9776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9776
  · intro a ha; simp [p9776] at ha; subst a; trivial
  · exact checked9776
theorem derived9776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9776 := by
  apply localUnsat_implies_entails f9776 [c9748, c9769, c9773, c9772, c9775, c3043, c1500] c9776 unsat9776 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9769 := derived9769 a h
  have h2 : Entails.eval a c9773 := derived9773 a h
  have h3 : Entails.eval a c9772 := derived9772 a h
  have h4 : Entails.eval a c9775 := derived9775 a h
  have h5 : Entails.eval a c3043 := h 3042 (by decide)
  have h6 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9777 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9768, some c9776, some c3595, some c3578, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9777 : lratChecker f9777 p9777 = .success := by decide +kernel
theorem unsat9777 : Unsatisfiable (PosFin 65) f9777 := by
  apply lratCheckerSound f9777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9777
  · intro a ha; simp [p9777] at ha; subst a; trivial
  · exact checked9777
theorem derived9777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9777 := by
  apply localUnsat_implies_entails f9777 [c9768, c9776, c3595, c3578] c9777 unsat9777 (by rfl) a
  have h0 : Entails.eval a c9768 := derived9768 a h
  have h1 : Entails.eval a c9776 := derived9776 a h
  have h2 : Entails.eval a c3595 := h 3594 (by decide)
  have h3 : Entails.eval a c3578 := h 3577 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9778 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3811, some c2024, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9778 : lratChecker f9778 p9778 = .success := by decide +kernel
theorem unsat9778 : Unsatisfiable (PosFin 65) f9778 := by
  apply lratCheckerSound f9778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9778
  · intro a ha; simp [p9778] at ha; subst a; trivial
  · exact checked9778
theorem derived9778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9778 := by
  apply localUnsat_implies_entails f9778 [c9748, c3811, c2024] c9778 unsat9778 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3811 := h 3810 (by decide)
  have h2 : Entails.eval a c2024 := h 2023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9779 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨58, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9259, some c2613, some c2810, some c3418, some c1884, some c1798, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9779 : lratChecker f9779 p9779 = .success := by decide +kernel
theorem unsat9779 : Unsatisfiable (PosFin 65) f9779 := by
  apply lratCheckerSound f9779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9779
  · intro a ha; simp [p9779] at ha; subst a; trivial
  · exact checked9779
theorem derived9779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9779 := by
  apply localUnsat_implies_entails f9779 [c9748, c9259, c2613, c2810, c3418, c1884, c1798] c9779 unsat9779 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9259 := derived9259 a h
  have h2 : Entails.eval a c2613 := h 2612 (by decide)
  have h3 : Entails.eval a c2810 := h 2809 (by decide)
  have h4 : Entails.eval a c3418 := h 3417 (by decide)
  have h5 : Entails.eval a c1884 := h 1883 (by decide)
  have h6 : Entails.eval a c1798 := h 1797 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9780 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9778, some c9779, some c5044, some c4392, some c1883, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9780 : lratChecker f9780 p9780 = .success := by decide +kernel
theorem unsat9780 : Unsatisfiable (PosFin 65) f9780 := by
  apply lratCheckerSound f9780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9780
  · intro a ha; simp [p9780] at ha; subst a; trivial
  · exact checked9780
theorem derived9780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9780 := by
  apply localUnsat_implies_entails f9780 [c9748, c9778, c9779, c5044, c4392, c1883] c9780 unsat9780 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9778 := derived9778 a h
  have h2 : Entails.eval a c9779 := derived9779 a h
  have h3 : Entails.eval a c5044 := h 5043 (by decide)
  have h4 : Entails.eval a c4392 := h 4391 (by decide)
  have h5 : Entails.eval a c1883 := h 1882 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9781 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9259, some c2613, some c2810, some c4119, some c9752, some c1906, some c1656, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9781 : lratChecker f9781 p9781 = .success := by decide +kernel
theorem unsat9781 : Unsatisfiable (PosFin 65) f9781 := by
  apply lratCheckerSound f9781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9781
  · intro a ha; simp [p9781] at ha; subst a; trivial
  · exact checked9781
theorem derived9781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9781 := by
  apply localUnsat_implies_entails f9781 [c9748, c9259, c2613, c2810, c4119, c9752, c1906, c1656] c9781 unsat9781 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9259 := derived9259 a h
  have h2 : Entails.eval a c2613 := h 2612 (by decide)
  have h3 : Entails.eval a c2810 := h 2809 (by decide)
  have h4 : Entails.eval a c4119 := h 4118 (by decide)
  have h5 : Entails.eval a c9752 := derived9752 a h
  have h6 : Entails.eval a c1906 := h 1905 (by decide)
  have h7 : Entails.eval a c1656 := h 1655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9782 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3816, some c2024, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9782 : lratChecker f9782 p9782 = .success := by decide +kernel
theorem unsat9782 : Unsatisfiable (PosFin 65) f9782 := by
  apply lratCheckerSound f9782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9782
  · intro a ha; simp [p9782] at ha; subst a; trivial
  · exact checked9782
theorem derived9782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9782 := by
  apply localUnsat_implies_entails f9782 [c9748, c3816, c2024] c9782 unsat9782 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3816 := h 3815 (by decide)
  have h2 : Entails.eval a c2024 := h 2023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9783 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9777, some c9780, some c9769, some c9782, some c9781, some c9775, some c4125, some c1500, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9783 : lratChecker f9783 p9783 = .success := by decide +kernel
theorem unsat9783 : Unsatisfiable (PosFin 65) f9783 := by
  apply lratCheckerSound f9783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9783
  · intro a ha; simp [p9783] at ha; subst a; trivial
  · exact checked9783
theorem derived9783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9783 := by
  apply localUnsat_implies_entails f9783 [c9748, c9777, c9780, c9769, c9782, c9781, c9775, c4125, c1500] c9783 unsat9783 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9777 := derived9777 a h
  have h2 : Entails.eval a c9780 := derived9780 a h
  have h3 : Entails.eval a c9769 := derived9769 a h
  have h4 : Entails.eval a c9782 := derived9782 a h
  have h5 : Entails.eval a c9781 := derived9781 a h
  have h6 : Entails.eval a c9775 := derived9775 a h
  have h7 : Entails.eval a c4125 := h 4124 (by decide)
  have h8 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9784 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9777, some c9783, some c3595, some c9759, some c3578, some c9756, some c3591, some c9779, some c3597, some c9750, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9784 : lratChecker f9784 p9784 = .success := by decide +kernel
theorem unsat9784 : Unsatisfiable (PosFin 65) f9784 := by
  apply lratCheckerSound f9784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9784
  · intro a ha; simp [p9784] at ha; subst a; trivial
  · exact checked9784
theorem derived9784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9784 := by
  apply localUnsat_implies_entails f9784 [c9777, c9783, c3595, c9759, c3578, c9756, c3591, c9779, c3597, c9750] c9784 unsat9784 (by rfl) a
  have h0 : Entails.eval a c9777 := derived9777 a h
  have h1 : Entails.eval a c9783 := derived9783 a h
  have h2 : Entails.eval a c3595 := h 3594 (by decide)
  have h3 : Entails.eval a c9759 := derived9759 a h
  have h4 : Entails.eval a c3578 := h 3577 (by decide)
  have h5 : Entails.eval a c9756 := derived9756 a h
  have h6 : Entails.eval a c3591 := h 3590 (by decide)
  have h7 : Entails.eval a c9779 := derived9779 a h
  have h8 : Entails.eval a c3597 := h 3596 (by decide)
  have h9 : Entails.eval a c9750 := derived9750 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9785 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9215, some c9210, some c9212, some c3245, some c9447, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p9785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9785 : lratChecker f9785 p9785 = .success := by decide +kernel
theorem unsat9785 : Unsatisfiable (PosFin 65) f9785 := by
  apply lratCheckerSound f9785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9785
  · intro a ha; simp [p9785] at ha; subst a; trivial
  · exact checked9785
theorem derived9785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9785 := by
  apply localUnsat_implies_entails f9785 [c9215, c9210, c9212, c3245, c9447] c9785 unsat9785 (by rfl) a
  have h0 : Entails.eval a c9215 := derived9215 a h
  have h1 : Entails.eval a c9210 := derived9210 a h
  have h2 : Entails.eval a c9212 := derived9212 a h
  have h3 : Entails.eval a c3245 := h 3244 (by decide)
  have h4 : Entails.eval a c9447 := derived9447 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9786 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5044, some c4392, some c3130, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9786 : lratChecker f9786 p9786 = .success := by decide +kernel
theorem unsat9786 : Unsatisfiable (PosFin 65) f9786 := by
  apply lratCheckerSound f9786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9786
  · intro a ha; simp [p9786] at ha; subst a; trivial
  · exact checked9786
theorem derived9786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9786 := by
  apply localUnsat_implies_entails f9786 [c5044, c4392, c3130] c9786 unsat9786 (by rfl) a
  have h0 : Entails.eval a c5044 := h 5043 (by decide)
  have h1 : Entails.eval a c4392 := h 4391 (by decide)
  have h2 : Entails.eval a c3130 := h 3129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9787 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9782, some c9761, some c9781, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9787 : lratChecker f9787 p9787 = .success := by decide +kernel
theorem unsat9787 : Unsatisfiable (PosFin 65) f9787 := by
  apply lratCheckerSound f9787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9787
  · intro a ha; simp [p9787] at ha; subst a; trivial
  · exact checked9787
theorem derived9787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9787 := by
  apply localUnsat_implies_entails f9787 [c9782, c9761, c9781] c9787 unsat9787 (by rfl) a
  have h0 : Entails.eval a c9782 := derived9782 a h
  have h1 : Entails.eval a c9761 := derived9761 a h
  have h2 : Entails.eval a c9781 := derived9781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9788 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9784, some c9785, some c9786, some c9787, some c9759, some c3591, some c3597, some c9750, some c9259, some c9339, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9788 : lratChecker f9788 p9788 = .success := by decide +kernel
theorem unsat9788 : Unsatisfiable (PosFin 65) f9788 := by
  apply lratCheckerSound f9788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9788
  · intro a ha; simp [p9788] at ha; subst a; trivial
  · exact checked9788
theorem derived9788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9788 := by
  apply localUnsat_implies_entails f9788 [c9784, c9785, c9786, c9787, c9759, c3591, c3597, c9750, c9259, c9339] c9788 unsat9788 (by rfl) a
  have h0 : Entails.eval a c9784 := derived9784 a h
  have h1 : Entails.eval a c9785 := derived9785 a h
  have h2 : Entails.eval a c9786 := derived9786 a h
  have h3 : Entails.eval a c9787 := derived9787 a h
  have h4 : Entails.eval a c9759 := derived9759 a h
  have h5 : Entails.eval a c3591 := h 3590 (by decide)
  have h6 : Entails.eval a c3597 := h 3596 (by decide)
  have h7 : Entails.eval a c9750 := derived9750 a h
  have h8 : Entails.eval a c9259 := derived9259 a h
  have h9 : Entails.eval a c9339 := derived9339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9789 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨58, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1523, some c4136, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9789 : lratChecker f9789 p9789 = .success := by decide +kernel
theorem unsat9789 : Unsatisfiable (PosFin 65) f9789 := by
  apply lratCheckerSound f9789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9789
  · intro a ha; simp [p9789] at ha; subst a; trivial
  · exact checked9789
theorem derived9789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9789 := by
  apply localUnsat_implies_entails f9789 [c9748, c1523, c4136] c9789 unsat9789 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1523 := h 1522 (by decide)
  have h2 : Entails.eval a c4136 := h 4135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9790 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨57, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1519, some c2015, some c4117, some c4245, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9790 : lratChecker f9790 p9790 = .success := by decide +kernel
theorem unsat9790 : Unsatisfiable (PosFin 65) f9790 := by
  apply lratCheckerSound f9790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9790
  · intro a ha; simp [p9790] at ha; subst a; trivial
  · exact checked9790
theorem derived9790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9790 := by
  apply localUnsat_implies_entails f9790 [c9748, c1519, c2015, c4117, c4245] c9790 unsat9790 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1519 := h 1518 (by decide)
  have h2 : Entails.eval a c2015 := h 2014 (by decide)
  have h3 : Entails.eval a c4117 := h 4116 (by decide)
  have h4 : Entails.eval a c4245 := h 4244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9791 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9782, some c9787, some c9761, some c9790, some c4125, some c1500, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9791 : lratChecker f9791 p9791 = .success := by decide +kernel
theorem unsat9791 : Unsatisfiable (PosFin 65) f9791 := by
  apply lratCheckerSound f9791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9791
  · intro a ha; simp [p9791] at ha; subst a; trivial
  · exact checked9791
theorem derived9791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9791 := by
  apply localUnsat_implies_entails f9791 [c9748, c9782, c9787, c9761, c9790, c4125, c1500] c9791 unsat9791 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9782 := derived9782 a h
  have h2 : Entails.eval a c9787 := derived9787 a h
  have h3 : Entails.eval a c9761 := derived9761 a h
  have h4 : Entails.eval a c9790 := derived9790 a h
  have h5 : Entails.eval a c4125 := h 4124 (by decide)
  have h6 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9792 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9784, some c9785, some c9788, some c9791, some c3595, some c3578, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p9792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9792 : lratChecker f9792 p9792 = .success := by decide +kernel
theorem unsat9792 : Unsatisfiable (PosFin 65) f9792 := by
  apply lratCheckerSound f9792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9792
  · intro a ha; simp [p9792] at ha; subst a; trivial
  · exact checked9792
theorem derived9792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9792 := by
  apply localUnsat_implies_entails f9792 [c9784, c9785, c9788, c9791, c3595, c3578] c9792 unsat9792 (by rfl) a
  have h0 : Entails.eval a c9784 := derived9784 a h
  have h1 : Entails.eval a c9785 := derived9785 a h
  have h2 : Entails.eval a c9788 := derived9788 a h
  have h3 : Entails.eval a c9791 := derived9791 a h
  have h4 : Entails.eval a c3595 := h 3594 (by decide)
  have h5 : Entails.eval a c3578 := h 3577 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9793 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9352, some c4611, some c2731, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9793 : lratChecker f9793 p9793 = .success := by decide +kernel
theorem unsat9793 : Unsatisfiable (PosFin 65) f9793 := by
  apply lratCheckerSound f9793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9793
  · intro a ha; simp [p9793] at ha; subst a; trivial
  · exact checked9793
theorem derived9793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9793 := by
  apply localUnsat_implies_entails f9793 [c9352, c4611, c2731] c9793 unsat9793 (by rfl) a
  have h0 : Entails.eval a c9352 := derived9352 a h
  have h1 : Entails.eval a c4611 := h 4610 (by decide)
  have h2 : Entails.eval a c2731 := h 2730 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9794 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3795, some c2020, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9794 : lratChecker f9794 p9794 = .success := by decide +kernel
theorem unsat9794 : Unsatisfiable (PosFin 65) f9794 := by
  apply lratCheckerSound f9794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9794
  · intro a ha; simp [p9794] at ha; subst a; trivial
  · exact checked9794
theorem derived9794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9794 := by
  apply localUnsat_implies_entails f9794 [c9748, c3795, c2020] c9794 unsat9794 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3795 := h 3794 (by decide)
  have h2 : Entails.eval a c2020 := h 2019 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9795 : DefaultClause 65 := directClause [(⟨61, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4636, some c4554, some c2752, some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9795 : lratChecker f9795 p9795 = .success := by decide +kernel
theorem unsat9795 : Unsatisfiable (PosFin 65) f9795 := by
  apply lratCheckerSound f9795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9795
  · intro a ha; simp [p9795] at ha; subst a; trivial
  · exact checked9795
theorem derived9795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9795 := by
  apply localUnsat_implies_entails f9795 [c4636, c4554, c2752] c9795 unsat9795 (by rfl) a
  have h0 : Entails.eval a c4636 := h 4635 (by decide)
  have h1 : Entails.eval a c4554 := h 4553 (by decide)
  have h2 : Entails.eval a c2752 := h 2751 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9796 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4612, some c4624, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9796 : lratChecker f9796 p9796 = .success := by decide +kernel
theorem unsat9796 : Unsatisfiable (PosFin 65) f9796 := by
  apply lratCheckerSound f9796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9796
  · intro a ha; simp [p9796] at ha; subst a; trivial
  · exact checked9796
theorem derived9796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9796 := by
  apply localUnsat_implies_entails f9796 [c4612, c4624] c9796 unsat9796 (by rfl) a
  have h0 : Entails.eval a c4612 := h 4611 (by decide)
  have h1 : Entails.eval a c4624 := h 4623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9797 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2730, some c2896, some c4855, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9797 : lratChecker f9797 p9797 = .success := by decide +kernel
theorem unsat9797 : Unsatisfiable (PosFin 65) f9797 := by
  apply lratCheckerSound f9797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9797
  · intro a ha; simp [p9797] at ha; subst a; trivial
  · exact checked9797
theorem derived9797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9797 := by
  apply localUnsat_implies_entails f9797 [c2730, c2896, c4855] c9797 unsat9797 (by rfl) a
  have h0 : Entails.eval a c2730 := h 2729 (by decide)
  have h1 : Entails.eval a c2896 := h 2895 (by decide)
  have h2 : Entails.eval a c4855 := h 4854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9798 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9793, some c9796, some c9797, some c8001, some c4552, some c2740, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9798 : lratChecker f9798 p9798 = .success := by decide +kernel
theorem unsat9798 : Unsatisfiable (PosFin 65) f9798 := by
  apply lratCheckerSound f9798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9798
  · intro a ha; simp [p9798] at ha; subst a; trivial
  · exact checked9798
theorem derived9798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9798 := by
  apply localUnsat_implies_entails f9798 [c9793, c9796, c9797, c8001, c4552, c2740] c9798 unsat9798 (by rfl) a
  have h0 : Entails.eval a c9793 := derived9793 a h
  have h1 : Entails.eval a c9796 := derived9796 a h
  have h2 : Entails.eval a c9797 := derived9797 a h
  have h3 : Entails.eval a c8001 := derived8001 a h
  have h4 : Entails.eval a c4552 := h 4551 (by decide)
  have h5 : Entails.eval a c2740 := h 2739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9799 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4620, some c4627, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9799 : lratChecker f9799 p9799 = .success := by decide +kernel
theorem unsat9799 : Unsatisfiable (PosFin 65) f9799 := by
  apply lratCheckerSound f9799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9799
  · intro a ha; simp [p9799] at ha; subst a; trivial
  · exact checked9799
theorem derived9799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9799 := by
  apply localUnsat_implies_entails f9799 [c4620, c4627] c9799 unsat9799 (by rfl) a
  have h0 : Entails.eval a c4620 := h 4619 (by decide)
  have h1 : Entails.eval a c4627 := h 4626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9800 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1945, some c4551, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9800 : lratChecker f9800 p9800 = .success := by decide +kernel
theorem unsat9800 : Unsatisfiable (PosFin 65) f9800 := by
  apply lratCheckerSound f9800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9800
  · intro a ha; simp [p9800] at ha; subst a; trivial
  · exact checked9800
theorem derived9800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9800 := by
  apply localUnsat_implies_entails f9800 [c9748, c1945, c4551] c9800 unsat9800 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1945 := h 1944 (by decide)
  have h2 : Entails.eval a c4551 := h 4550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9801 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9792, some c9795, some c9794, some c9755, some c9798, some c9775, some c9799, some c9800, some c2759, some c2755, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9801 : lratChecker f9801 p9801 = .success := by decide +kernel
theorem unsat9801 : Unsatisfiable (PosFin 65) f9801 := by
  apply lratCheckerSound f9801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9801
  · intro a ha; simp [p9801] at ha; subst a; trivial
  · exact checked9801
theorem derived9801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9801 := by
  apply localUnsat_implies_entails f9801 [c9792, c9795, c9794, c9755, c9798, c9775, c9799, c9800, c2759, c2755] c9801 unsat9801 (by rfl) a
  have h0 : Entails.eval a c9792 := derived9792 a h
  have h1 : Entails.eval a c9795 := derived9795 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9755 := derived9755 a h
  have h4 : Entails.eval a c9798 := derived9798 a h
  have h5 : Entails.eval a c9775 := derived9775 a h
  have h6 : Entails.eval a c9799 := derived9799 a h
  have h7 : Entails.eval a c9800 := derived9800 a h
  have h8 : Entails.eval a c2759 := h 2758 (by decide)
  have h9 : Entails.eval a c2755 := h 2754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9802 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4581, some c4584, some c4845, some c4846, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9802 : lratChecker f9802 p9802 = .success := by decide +kernel
theorem unsat9802 : Unsatisfiable (PosFin 65) f9802 := by
  apply lratCheckerSound f9802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9802
  · intro a ha; simp [p9802] at ha; subst a; trivial
  · exact checked9802
theorem derived9802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9802 := by
  apply localUnsat_implies_entails f9802 [c4581, c4584, c4845, c4846] c9802 unsat9802 (by rfl) a
  have h0 : Entails.eval a c4581 := h 4580 (by decide)
  have h1 : Entails.eval a c4584 := h 4583 (by decide)
  have h2 : Entails.eval a c4845 := h 4844 (by decide)
  have h3 : Entails.eval a c4846 := h 4845 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9803 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c5112, some c5114, some c5113, some c1703, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9803 : lratChecker f9803 p9803 = .success := by decide +kernel
theorem unsat9803 : Unsatisfiable (PosFin 65) f9803 := by
  apply lratCheckerSound f9803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9803
  · intro a ha; simp [p9803] at ha; subst a; trivial
  · exact checked9803
theorem derived9803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9803 := by
  apply localUnsat_implies_entails f9803 [c9748, c5112, c5114, c5113, c1703] c9803 unsat9803 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c5112 := h 5111 (by decide)
  have h2 : Entails.eval a c5114 := h 5113 (by decide)
  have h3 : Entails.eval a c5113 := h 5112 (by decide)
  have h4 : Entails.eval a c1703 := h 1702 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9804 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1544, some c4591, some c4590, some c1554, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9804 : lratChecker f9804 p9804 = .success := by decide +kernel
theorem unsat9804 : Unsatisfiable (PosFin 65) f9804 := by
  apply lratCheckerSound f9804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9804
  · intro a ha; simp [p9804] at ha; subst a; trivial
  · exact checked9804
theorem derived9804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9804 := by
  apply localUnsat_implies_entails f9804 [c9748, c1544, c4591, c4590, c1554] c9804 unsat9804 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1544 := h 1543 (by decide)
  have h2 : Entails.eval a c4591 := h 4590 (by decide)
  have h3 : Entails.eval a c4590 := h 4589 (by decide)
  have h4 : Entails.eval a c1554 := h 1553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9805 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c5112, some c5114, some c5113, some c3973, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9805 : lratChecker f9805 p9805 = .success := by decide +kernel
theorem unsat9805 : Unsatisfiable (PosFin 65) f9805 := by
  apply lratCheckerSound f9805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9805
  · intro a ha; simp [p9805] at ha; subst a; trivial
  · exact checked9805
theorem derived9805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9805 := by
  apply localUnsat_implies_entails f9805 [c5112, c5114, c5113, c3973] c9805 unsat9805 (by rfl) a
  have h0 : Entails.eval a c5112 := h 5111 (by decide)
  have h1 : Entails.eval a c5114 := h 5113 (by decide)
  have h2 : Entails.eval a c5113 := h 5112 (by decide)
  have h3 : Entails.eval a c3973 := h 3972 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9806 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3972, some c4591, some c4590, some c9805, some c1626, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9806 : lratChecker f9806 p9806 = .success := by decide +kernel
theorem unsat9806 : Unsatisfiable (PosFin 65) f9806 := by
  apply lratCheckerSound f9806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9806
  · intro a ha; simp [p9806] at ha; subst a; trivial
  · exact checked9806
theorem derived9806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9806 := by
  apply localUnsat_implies_entails f9806 [c9748, c3972, c4591, c4590, c9805, c1626] c9806 unsat9806 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3972 := h 3971 (by decide)
  have h2 : Entails.eval a c4591 := h 4590 (by decide)
  have h3 : Entails.eval a c4590 := h 4589 (by decide)
  have h4 : Entails.eval a c9805 := derived9805 a h
  have h5 : Entails.eval a c1626 := h 1625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9807 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9806, some c4581, some c4584, some c4535, some c3398, some c4537, some c3400, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9807 : lratChecker f9807 p9807 = .success := by decide +kernel
theorem unsat9807 : Unsatisfiable (PosFin 65) f9807 := by
  apply lratCheckerSound f9807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9807
  · intro a ha; simp [p9807] at ha; subst a; trivial
  · exact checked9807
theorem derived9807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9807 := by
  apply localUnsat_implies_entails f9807 [c9806, c4581, c4584, c4535, c3398, c4537, c3400] c9807 unsat9807 (by rfl) a
  have h0 : Entails.eval a c9806 := derived9806 a h
  have h1 : Entails.eval a c4581 := h 4580 (by decide)
  have h2 : Entails.eval a c4584 := h 4583 (by decide)
  have h3 : Entails.eval a c4535 := h 4534 (by decide)
  have h4 : Entails.eval a c3398 := h 3397 (by decide)
  have h5 : Entails.eval a c4537 := h 4536 (by decide)
  have h6 : Entails.eval a c3400 := h 3399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9808 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9807, some c9804, some c1585, some c9802, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9808 : lratChecker f9808 p9808 = .success := by decide +kernel
theorem unsat9808 : Unsatisfiable (PosFin 65) f9808 := by
  apply lratCheckerSound f9808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9808
  · intro a ha; simp [p9808] at ha; subst a; trivial
  · exact checked9808
theorem derived9808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9808 := by
  apply localUnsat_implies_entails f9808 [c9748, c9807, c9804, c1585, c9802] c9808 unsat9808 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9807 := derived9807 a h
  have h2 : Entails.eval a c9804 := derived9804 a h
  have h3 : Entails.eval a c1585 := h 1584 (by decide)
  have h4 : Entails.eval a c9802 := derived9802 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9809 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4591, some c4589, some c4590, some c4599, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9809 : lratChecker f9809 p9809 = .success := by decide +kernel
theorem unsat9809 : Unsatisfiable (PosFin 65) f9809 := by
  apply lratCheckerSound f9809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9809
  · intro a ha; simp [p9809] at ha; subst a; trivial
  · exact checked9809
theorem derived9809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9809 := by
  apply localUnsat_implies_entails f9809 [c4591, c4589, c4590, c4599] c9809 unsat9809 (by rfl) a
  have h0 : Entails.eval a c4591 := h 4590 (by decide)
  have h1 : Entails.eval a c4589 := h 4588 (by decide)
  have h2 : Entails.eval a c4590 := h 4589 (by decide)
  have h3 : Entails.eval a c4599 := h 4598 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9810 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨12, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9809, some c4583, some c4582, some c4596, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9810 : lratChecker f9810 p9810 = .success := by decide +kernel
theorem unsat9810 : Unsatisfiable (PosFin 65) f9810 := by
  apply lratCheckerSound f9810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9810
  · intro a ha; simp [p9810] at ha; subst a; trivial
  · exact checked9810
theorem derived9810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9810 := by
  apply localUnsat_implies_entails f9810 [c9809, c4583, c4582, c4596] c9810 unsat9810 (by rfl) a
  have h0 : Entails.eval a c9809 := derived9809 a h
  have h1 : Entails.eval a c4583 := h 4582 (by decide)
  have h2 : Entails.eval a c4582 := h 4581 (by decide)
  have h3 : Entails.eval a c4596 := h 4595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9811 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9793, some c9795, some c4629, some c4622, some c4645, some c9810, some c4581, some c4584, some c4587, some c4588, some c4597, some c4595, some c4594, some c4593, some c8977, some c1481, some c9808, some c804, some c923, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9811 : lratChecker f9811 p9811 = .success := by decide +kernel
theorem unsat9811 : Unsatisfiable (PosFin 65) f9811 := by
  apply lratCheckerSound f9811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9811
  · intro a ha; simp [p9811] at ha; subst a; trivial
  · exact checked9811
theorem derived9811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9811 := by
  apply localUnsat_implies_entails f9811 [c9748, c9793, c9795, c4629, c4622, c4645, c9810, c4581, c4584, c4587, c4588, c4597, c4595, c4594, c4593, c8977, c1481, c9808, c804, c923] c9811 unsat9811 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9793 := derived9793 a h
  have h2 : Entails.eval a c9795 := derived9795 a h
  have h3 : Entails.eval a c4629 := h 4628 (by decide)
  have h4 : Entails.eval a c4622 := h 4621 (by decide)
  have h5 : Entails.eval a c4645 := h 4644 (by decide)
  have h6 : Entails.eval a c9810 := derived9810 a h
  have h7 : Entails.eval a c4581 := h 4580 (by decide)
  have h8 : Entails.eval a c4584 := h 4583 (by decide)
  have h9 : Entails.eval a c4587 := h 4586 (by decide)
  have h10 : Entails.eval a c4588 := h 4587 (by decide)
  have h11 : Entails.eval a c4597 := h 4596 (by decide)
  have h12 : Entails.eval a c4595 := h 4594 (by decide)
  have h13 : Entails.eval a c4594 := h 4593 (by decide)
  have h14 : Entails.eval a c4593 := h 4592 (by decide)
  have h15 : Entails.eval a c8977 := derived8977 a h
  have h16 : Entails.eval a c1481 := h 1480 (by decide)
  have h17 : Entails.eval a c9808 := derived9808 a h
  have h18 : Entails.eval a c804 := h 803 (by decide)
  have h19 : Entails.eval a c923 := h 922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9812 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1465, some c1466, some c1467, some c1930, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p9812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9812 : lratChecker f9812 p9812 = .success := by decide +kernel
theorem unsat9812 : Unsatisfiable (PosFin 65) f9812 := by
  apply lratCheckerSound f9812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9812
  · intro a ha; simp [p9812] at ha; subst a; trivial
  · exact checked9812
theorem derived9812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9812 := by
  apply localUnsat_implies_entails f9812 [c9748, c1465, c1466, c1467, c1930] c9812 unsat9812 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1465 := h 1464 (by decide)
  have h2 : Entails.eval a c1466 := h 1465 (by decide)
  have h3 : Entails.eval a c1467 := h 1466 (by decide)
  have h4 : Entails.eval a c1930 := h 1929 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9813 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9812, some c1454, some c1918, some c4531, some c4537, some c4535, some c1462, some c1455, some c4542, some c1479, some c1486, some c1456, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9813 : lratChecker f9813 p9813 = .success := by decide +kernel
theorem unsat9813 : Unsatisfiable (PosFin 65) f9813 := by
  apply lratCheckerSound f9813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9813
  · intro a ha; simp [p9813] at ha; subst a; trivial
  · exact checked9813
theorem derived9813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9813 := by
  apply localUnsat_implies_entails f9813 [c9748, c9812, c1454, c1918, c4531, c4537, c4535, c1462, c1455, c4542, c1479, c1486, c1456] c9813 unsat9813 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9812 := derived9812 a h
  have h2 : Entails.eval a c1454 := h 1453 (by decide)
  have h3 : Entails.eval a c1918 := h 1917 (by decide)
  have h4 : Entails.eval a c4531 := h 4530 (by decide)
  have h5 : Entails.eval a c4537 := h 4536 (by decide)
  have h6 : Entails.eval a c4535 := h 4534 (by decide)
  have h7 : Entails.eval a c1462 := h 1461 (by decide)
  have h8 : Entails.eval a c1455 := h 1454 (by decide)
  have h9 : Entails.eval a c4542 := h 4541 (by decide)
  have h10 : Entails.eval a c1479 := h 1478 (by decide)
  have h11 : Entails.eval a c1486 := h 1485 (by decide)
  have h12 : Entails.eval a c1456 := h 1455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9814 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1939, some c1530, some c9813, some c1457, some c1458, some c4530, some c3778, some c4649, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9814 : lratChecker f9814 p9814 = .success := by decide +kernel
theorem unsat9814 : Unsatisfiable (PosFin 65) f9814 := by
  apply lratCheckerSound f9814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9814
  · intro a ha; simp [p9814] at ha; subst a; trivial
  · exact checked9814
theorem derived9814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9814 := by
  apply localUnsat_implies_entails f9814 [c9748, c1939, c1530, c9813, c1457, c1458, c4530, c3778, c4649] c9814 unsat9814 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1939 := h 1938 (by decide)
  have h2 : Entails.eval a c1530 := h 1529 (by decide)
  have h3 : Entails.eval a c9813 := derived9813 a h
  have h4 : Entails.eval a c1457 := h 1456 (by decide)
  have h5 : Entails.eval a c1458 := h 1457 (by decide)
  have h6 : Entails.eval a c4530 := h 4529 (by decide)
  have h7 : Entails.eval a c3778 := h 3777 (by decide)
  have h8 : Entails.eval a c4649 := h 4648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9815 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1920, some c1919, some c4536, some c3034, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9815 : lratChecker f9815 p9815 = .success := by decide +kernel
theorem unsat9815 : Unsatisfiable (PosFin 65) f9815 := by
  apply lratCheckerSound f9815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9815
  · intro a ha; simp [p9815] at ha; subst a; trivial
  · exact checked9815
theorem derived9815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9815 := by
  apply localUnsat_implies_entails f9815 [c9748, c1920, c1919, c4536, c3034] c9815 unsat9815 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1920 := h 1919 (by decide)
  have h2 : Entails.eval a c1919 := h 1918 (by decide)
  have h3 : Entails.eval a c4536 := h 4535 (by decide)
  have h4 : Entails.eval a c3034 := h 3033 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9816 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9815, some c1918, some c4531, some c4537, some c4534, some c4535, some c4542, some c8977, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9816 : lratChecker f9816 p9816 = .success := by decide +kernel
theorem unsat9816 : Unsatisfiable (PosFin 65) f9816 := by
  apply lratCheckerSound f9816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9816
  · intro a ha; simp [p9816] at ha; subst a; trivial
  · exact checked9816
theorem derived9816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9816 := by
  apply localUnsat_implies_entails f9816 [c9748, c9815, c1918, c4531, c4537, c4534, c4535, c4542, c8977] c9816 unsat9816 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9815 := derived9815 a h
  have h2 : Entails.eval a c1918 := h 1917 (by decide)
  have h3 : Entails.eval a c4531 := h 4530 (by decide)
  have h4 : Entails.eval a c4537 := h 4536 (by decide)
  have h5 : Entails.eval a c4534 := h 4533 (by decide)
  have h6 : Entails.eval a c4535 := h 4534 (by decide)
  have h7 : Entails.eval a c4542 := h 4541 (by decide)
  have h8 : Entails.eval a c8977 := derived8977 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9817 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9794, some c1939, some c9814, some c3051, some c9816, some c3029, some c3027, some c3028, some c3030, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9817 : lratChecker f9817 p9817 = .success := by decide +kernel
theorem unsat9817 : Unsatisfiable (PosFin 65) f9817 := by
  apply lratCheckerSound f9817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9817
  · intro a ha; simp [p9817] at ha; subst a; trivial
  · exact checked9817
theorem derived9817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9817 := by
  apply localUnsat_implies_entails f9817 [c9748, c9794, c1939, c9814, c3051, c9816, c3029, c3027, c3028, c3030] c9817 unsat9817 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c1939 := h 1938 (by decide)
  have h3 : Entails.eval a c9814 := derived9814 a h
  have h4 : Entails.eval a c3051 := h 3050 (by decide)
  have h5 : Entails.eval a c9816 := derived9816 a h
  have h6 : Entails.eval a c3029 := h 3028 (by decide)
  have h7 : Entails.eval a c3027 := h 3026 (by decide)
  have h8 : Entails.eval a c3028 := h 3027 (by decide)
  have h9 : Entails.eval a c3030 := h 3029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9818 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c910, some c909, some c1465, some c1478, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9818 : lratChecker f9818 p9818 = .success := by decide +kernel
theorem unsat9818 : Unsatisfiable (PosFin 65) f9818 := by
  apply lratCheckerSound f9818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9818
  · intro a ha; simp [p9818] at ha; subst a; trivial
  · exact checked9818
theorem derived9818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9818 := by
  apply localUnsat_implies_entails f9818 [c9748, c910, c909, c1465, c1478] c9818 unsat9818 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c910 := h 909 (by decide)
  have h2 : Entails.eval a c909 := h 908 (by decide)
  have h3 : Entails.eval a c1465 := h 1464 (by decide)
  have h4 : Entails.eval a c1478 := h 1477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9819 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9818, some c2720, some c2721, some c911, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9819 : lratChecker f9819 p9819 = .success := by decide +kernel
theorem unsat9819 : Unsatisfiable (PosFin 65) f9819 := by
  apply lratCheckerSound f9819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9819
  · intro a ha; simp [p9819] at ha; subst a; trivial
  · exact checked9819
theorem derived9819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9819 := by
  apply localUnsat_implies_entails f9819 [c9818, c2720, c2721, c911] c9819 unsat9819 (by rfl) a
  have h0 : Entails.eval a c9818 := derived9818 a h
  have h1 : Entails.eval a c2720 := h 2719 (by decide)
  have h2 : Entails.eval a c2721 := h 2720 (by decide)
  have h3 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9820 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨58, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2741, some c1530, some c9819, some c1457, some c1458, some c1479, some c1471, some c768, some c786, some c782, some c2723, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9820 : lratChecker f9820 p9820 = .success := by decide +kernel
theorem unsat9820 : Unsatisfiable (PosFin 65) f9820 := by
  apply lratCheckerSound f9820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9820
  · intro a ha; simp [p9820] at ha; subst a; trivial
  · exact checked9820
theorem derived9820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9820 := by
  apply localUnsat_implies_entails f9820 [c9748, c2741, c1530, c9819, c1457, c1458, c1479, c1471, c768, c786, c782, c2723] c9820 unsat9820 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2741 := h 2740 (by decide)
  have h2 : Entails.eval a c1530 := h 1529 (by decide)
  have h3 : Entails.eval a c9819 := derived9819 a h
  have h4 : Entails.eval a c1457 := h 1456 (by decide)
  have h5 : Entails.eval a c1458 := h 1457 (by decide)
  have h6 : Entails.eval a c1479 := h 1478 (by decide)
  have h7 : Entails.eval a c1471 := h 1470 (by decide)
  have h8 : Entails.eval a c768 := h 767 (by decide)
  have h9 : Entails.eval a c786 := h 785 (by decide)
  have h10 : Entails.eval a c782 := h 781 (by decide)
  have h11 : Entails.eval a c2723 := h 2722 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9821 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c975, some c910, some c909, some c833, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9821 : lratChecker f9821 p9821 = .success := by decide +kernel
theorem unsat9821 : Unsatisfiable (PosFin 65) f9821 := by
  apply lratCheckerSound f9821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9821
  · intro a ha; simp [p9821] at ha; subst a; trivial
  · exact checked9821
theorem derived9821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9821 := by
  apply localUnsat_implies_entails f9821 [c975, c910, c909, c833] c9821 unsat9821 (by rfl) a
  have h0 : Entails.eval a c975 := h 974 (by decide)
  have h1 : Entails.eval a c910 := h 909 (by decide)
  have h2 : Entails.eval a c909 := h 908 (by decide)
  have h3 : Entails.eval a c833 := h 832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9822 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9821, some c2720, some c2721, some c911, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9822 : lratChecker f9822 p9822 = .success := by decide +kernel
theorem unsat9822 : Unsatisfiable (PosFin 65) f9822 := by
  apply lratCheckerSound f9822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9822
  · intro a ha; simp [p9822] at ha; subst a; trivial
  · exact checked9822
theorem derived9822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9822 := by
  apply localUnsat_implies_entails f9822 [c9821, c2720, c2721, c911] c9822 unsat9822 (by rfl) a
  have h0 : Entails.eval a c9821 := derived9821 a h
  have h1 : Entails.eval a c2720 := h 2719 (by decide)
  have h2 : Entails.eval a c2721 := h 2720 (by decide)
  have h3 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9823 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9801, some c9792, some c9795, some c9794, some c9793, some c9811, some c9771, some c9817, some c2759, some c2741, some c9820, some c3051, some c9822, some c3029, some c3027, some c3028, some c3030, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9823 : lratChecker f9823 p9823 = .success := by decide +kernel
theorem unsat9823 : Unsatisfiable (PosFin 65) f9823 := by
  apply lratCheckerSound f9823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9823
  · intro a ha; simp [p9823] at ha; subst a; trivial
  · exact checked9823
theorem derived9823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9823 := by
  apply localUnsat_implies_entails f9823 [c9801, c9792, c9795, c9794, c9793, c9811, c9771, c9817, c2759, c2741, c9820, c3051, c9822, c3029, c3027, c3028, c3030] c9823 unsat9823 (by rfl) a
  have h0 : Entails.eval a c9801 := derived9801 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9795 := derived9795 a h
  have h3 : Entails.eval a c9794 := derived9794 a h
  have h4 : Entails.eval a c9793 := derived9793 a h
  have h5 : Entails.eval a c9811 := derived9811 a h
  have h6 : Entails.eval a c9771 := derived9771 a h
  have h7 : Entails.eval a c9817 := derived9817 a h
  have h8 : Entails.eval a c2759 := h 2758 (by decide)
  have h9 : Entails.eval a c2741 := h 2740 (by decide)
  have h10 : Entails.eval a c9820 := derived9820 a h
  have h11 : Entails.eval a c3051 := h 3050 (by decide)
  have h12 : Entails.eval a c9822 := derived9822 a h
  have h13 : Entails.eval a c3029 := h 3028 (by decide)
  have h14 : Entails.eval a c3027 := h 3026 (by decide)
  have h15 : Entails.eval a c3028 := h 3027 (by decide)
  have h16 : Entails.eval a c3030 := h 3029 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9824 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9792, some c9794, some c9801, some c9823, some c9775, some c3043, some c1500, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9824 : lratChecker f9824 p9824 = .success := by decide +kernel
theorem unsat9824 : Unsatisfiable (PosFin 65) f9824 := by
  apply lratCheckerSound f9824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9824
  · intro a ha; simp [p9824] at ha; subst a; trivial
  · exact checked9824
theorem derived9824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9824 := by
  apply localUnsat_implies_entails f9824 [c9748, c9792, c9794, c9801, c9823, c9775, c3043, c1500] c9824 unsat9824 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9801 := derived9801 a h
  have h4 : Entails.eval a c9823 := derived9823 a h
  have h5 : Entails.eval a c9775 := derived9775 a h
  have h6 : Entails.eval a c3043 := h 3042 (by decide)
  have h7 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9825 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c882, some c867, some c861, some c890, some c857, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9825 : lratChecker f9825 p9825 = .success := by decide +kernel
theorem unsat9825 : Unsatisfiable (PosFin 65) f9825 := by
  apply lratCheckerSound f9825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9825
  · intro a ha; simp [p9825] at ha; subst a; trivial
  · exact checked9825
theorem derived9825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9825 := by
  apply localUnsat_implies_entails f9825 [c882, c867, c861, c890, c857] c9825 unsat9825 (by rfl) a
  have h0 : Entails.eval a c882 := h 881 (by decide)
  have h1 : Entails.eval a c867 := h 866 (by decide)
  have h2 : Entails.eval a c861 := h 860 (by decide)
  have h3 : Entails.eval a c890 := h 889 (by decide)
  have h4 : Entails.eval a c857 := h 856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9826 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3560, some c9825, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9826 : lratChecker f9826 p9826 = .success := by decide +kernel
theorem unsat9826 : Unsatisfiable (PosFin 65) f9826 := by
  apply lratCheckerSound f9826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9826
  · intro a ha; simp [p9826] at ha; subst a; trivial
  · exact checked9826
theorem derived9826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9826 := by
  apply localUnsat_implies_entails f9826 [c3560, c9825] c9826 unsat9826 (by rfl) a
  have h0 : Entails.eval a c3560 := h 3559 (by decide)
  have h1 : Entails.eval a c9825 := derived9825 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9827 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9826, some c3546, some c3554, some c3551, some c854, some c883, some c879, some c878, some c862, some c858, some c866, some c3547, some c106, some c306, some c3576, some c100, some c3549, some c875, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9827 : lratChecker f9827 p9827 = .success := by decide +kernel
theorem unsat9827 : Unsatisfiable (PosFin 65) f9827 := by
  apply lratCheckerSound f9827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9827
  · intro a ha; simp [p9827] at ha; subst a; trivial
  · exact checked9827
theorem derived9827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9827 := by
  apply localUnsat_implies_entails f9827 [c9826, c3546, c3554, c3551, c854, c883, c879, c878, c862, c858, c866, c3547, c106, c306, c3576, c100, c3549, c875] c9827 unsat9827 (by rfl) a
  have h0 : Entails.eval a c9826 := derived9826 a h
  have h1 : Entails.eval a c3546 := h 3545 (by decide)
  have h2 : Entails.eval a c3554 := h 3553 (by decide)
  have h3 : Entails.eval a c3551 := h 3550 (by decide)
  have h4 : Entails.eval a c854 := h 853 (by decide)
  have h5 : Entails.eval a c883 := h 882 (by decide)
  have h6 : Entails.eval a c879 := h 878 (by decide)
  have h7 : Entails.eval a c878 := h 877 (by decide)
  have h8 : Entails.eval a c862 := h 861 (by decide)
  have h9 : Entails.eval a c858 := h 857 (by decide)
  have h10 : Entails.eval a c866 := h 865 (by decide)
  have h11 : Entails.eval a c3547 := h 3546 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c3576 := h 3575 (by decide)
  have h15 : Entails.eval a c100 := h 99 (by decide)
  have h16 : Entails.eval a c3549 := h 3548 (by decide)
  have h17 : Entails.eval a c875 := h 874 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9828 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3553, some c3550, some c3552, some c3558, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9828 : lratChecker f9828 p9828 = .success := by decide +kernel
theorem unsat9828 : Unsatisfiable (PosFin 65) f9828 := by
  apply lratCheckerSound f9828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9828
  · intro a ha; simp [p9828] at ha; subst a; trivial
  · exact checked9828
theorem derived9828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9828 := by
  apply localUnsat_implies_entails f9828 [c3553, c3550, c3552, c3558] c9828 unsat9828 (by rfl) a
  have h0 : Entails.eval a c3553 := h 3552 (by decide)
  have h1 : Entails.eval a c3550 := h 3549 (by decide)
  have h2 : Entails.eval a c3552 := h 3551 (by decide)
  have h3 : Entails.eval a c3558 := h 3557 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9829 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨63, by decide⟩, true), (⟨62, by decide⟩, true), (⟨60, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4307, some c1742, some c2787, some c1901, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9829 : lratChecker f9829 p9829 = .success := by decide +kernel
theorem unsat9829 : Unsatisfiable (PosFin 65) f9829 := by
  apply lratCheckerSound f9829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9829
  · intro a ha; simp [p9829] at ha; subst a; trivial
  · exact checked9829
theorem derived9829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9829 := by
  apply localUnsat_implies_entails f9829 [c9748, c4307, c1742, c2787, c1901] c9829 unsat9829 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4307 := h 4306 (by decide)
  have h2 : Entails.eval a c1742 := h 1741 (by decide)
  have h3 : Entails.eval a c2787 := h 2786 (by decide)
  have h4 : Entails.eval a c1901 := h 1900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9830 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9792, some c9824, some c3593, some c3592, some c3591, some c3580, some c3579, some c3590, some c8003, some c3587, some c3598, some c9828, some c9829, some c9827, some c3827, some c1666, some c3049, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9830 : lratChecker f9830 p9830 = .success := by decide +kernel
theorem unsat9830 : Unsatisfiable (PosFin 65) f9830 := by
  apply lratCheckerSound f9830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9830
  · intro a ha; simp [p9830] at ha; subst a; trivial
  · exact checked9830
theorem derived9830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9830 := by
  apply localUnsat_implies_entails f9830 [c9748, c9792, c9824, c3593, c3592, c3591, c3580, c3579, c3590, c8003, c3587, c3598, c9828, c9829, c9827, c3827, c1666, c3049] c9830 unsat9830 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9824 := derived9824 a h
  have h3 : Entails.eval a c3593 := h 3592 (by decide)
  have h4 : Entails.eval a c3592 := h 3591 (by decide)
  have h5 : Entails.eval a c3591 := h 3590 (by decide)
  have h6 : Entails.eval a c3580 := h 3579 (by decide)
  have h7 : Entails.eval a c3579 := h 3578 (by decide)
  have h8 : Entails.eval a c3590 := h 3589 (by decide)
  have h9 : Entails.eval a c8003 := derived8003 a h
  have h10 : Entails.eval a c3587 := h 3586 (by decide)
  have h11 : Entails.eval a c3598 := h 3597 (by decide)
  have h12 : Entails.eval a c9828 := derived9828 a h
  have h13 : Entails.eval a c9829 := derived9829 a h
  have h14 : Entails.eval a c9827 := derived9827 a h
  have h15 : Entails.eval a c3827 := h 3826 (by decide)
  have h16 : Entails.eval a c1666 := h 1665 (by decide)
  have h17 : Entails.eval a c3049 := h 3048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9831 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4630, some c9771, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9831 : lratChecker f9831 p9831 = .success := by decide +kernel
theorem unsat9831 : Unsatisfiable (PosFin 65) f9831 := by
  apply lratCheckerSound f9831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9831
  · intro a ha; simp [p9831] at ha; subst a; trivial
  · exact checked9831
theorem derived9831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9831 := by
  apply localUnsat_implies_entails f9831 [c4630, c9771] c9831 unsat9831 (by rfl) a
  have h0 : Entails.eval a c4630 := h 4629 (by decide)
  have h1 : Entails.eval a c9771 := derived9771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9832 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c4612, some c4627, some c9219, some c8003, some c4644, some c9810, some c4581, some c4584, some c4577, some c4587, some c4588, some c4597, some c4595, some c4594, some c4592, some c4604, some c4578, some c4603, some c4609, some c4579, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked9832 : lratChecker f9832 p9832 = .success := by decide +kernel
theorem unsat9832 : Unsatisfiable (PosFin 65) f9832 := by
  apply lratCheckerSound f9832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9832
  · intro a ha; simp [p9832] at ha; subst a; trivial
  · exact checked9832
theorem derived9832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9832 := by
  apply localUnsat_implies_entails f9832 [c9748, c4612, c4627, c9219, c8003, c4644, c9810, c4581, c4584, c4577, c4587, c4588, c4597, c4595, c4594, c4592, c4604, c4578, c4603, c4609, c4579] c9832 unsat9832 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c4612 := h 4611 (by decide)
  have h2 : Entails.eval a c4627 := h 4626 (by decide)
  have h3 : Entails.eval a c9219 := derived9219 a h
  have h4 : Entails.eval a c8003 := derived8003 a h
  have h5 : Entails.eval a c4644 := h 4643 (by decide)
  have h6 : Entails.eval a c9810 := derived9810 a h
  have h7 : Entails.eval a c4581 := h 4580 (by decide)
  have h8 : Entails.eval a c4584 := h 4583 (by decide)
  have h9 : Entails.eval a c4577 := h 4576 (by decide)
  have h10 : Entails.eval a c4587 := h 4586 (by decide)
  have h11 : Entails.eval a c4588 := h 4587 (by decide)
  have h12 : Entails.eval a c4597 := h 4596 (by decide)
  have h13 : Entails.eval a c4595 := h 4594 (by decide)
  have h14 : Entails.eval a c4594 := h 4593 (by decide)
  have h15 : Entails.eval a c4592 := h 4591 (by decide)
  have h16 : Entails.eval a c4604 := h 4603 (by decide)
  have h17 : Entails.eval a c4578 := h 4577 (by decide)
  have h18 : Entails.eval a c4603 := h 4602 (by decide)
  have h19 : Entails.eval a c4609 := h 4608 (by decide)
  have h20 : Entails.eval a c4579 := h 4578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9833 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9797, some c8001, some c9324, some c2740, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9833 : lratChecker f9833 p9833 = .success := by decide +kernel
theorem unsat9833 : Unsatisfiable (PosFin 65) f9833 := by
  apply lratCheckerSound f9833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9833
  · intro a ha; simp [p9833] at ha; subst a; trivial
  · exact checked9833
theorem derived9833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9833 := by
  apply localUnsat_implies_entails f9833 [c9797, c8001, c9324, c2740] c9833 unsat9833 (by rfl) a
  have h0 : Entails.eval a c9797 := derived9797 a h
  have h1 : Entails.eval a c8001 := derived8001 a h
  have h2 : Entails.eval a c9324 := derived9324 a h
  have h3 : Entails.eval a c2740 := h 2739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9834 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2731, some c2759, some c9820, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9834 : lratChecker f9834 p9834 = .success := by decide +kernel
theorem unsat9834 : Unsatisfiable (PosFin 65) f9834 := by
  apply lratCheckerSound f9834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9834
  · intro a ha; simp [p9834] at ha; subst a; trivial
  · exact checked9834
theorem derived9834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9834 := by
  apply localUnsat_implies_entails f9834 [c2731, c2759, c9820] c9834 unsat9834 (by rfl) a
  have h0 : Entails.eval a c2731 := h 2730 (by decide)
  have h1 : Entails.eval a c2759 := h 2758 (by decide)
  have h2 : Entails.eval a c9820 := derived9820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9835 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9795, some c9794, some c9834, some c4546, some c9814, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9835 : lratChecker f9835 p9835 = .success := by decide +kernel
theorem unsat9835 : Unsatisfiable (PosFin 65) f9835 := by
  apply lratCheckerSound f9835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9835
  · intro a ha; simp [p9835] at ha; subst a; trivial
  · exact checked9835
theorem derived9835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9835 := by
  apply localUnsat_implies_entails f9835 [c9795, c9794, c9834, c4546, c9814] c9835 unsat9835 (by rfl) a
  have h0 : Entails.eval a c9795 := derived9795 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9834 := derived9834 a h
  have h3 : Entails.eval a c4546 := h 4545 (by decide)
  have h4 : Entails.eval a c9814 := derived9814 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9836 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨58, by decide⟩, true), (⟨63, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4669, some c3820, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9836 : lratChecker f9836 p9836 = .success := by decide +kernel
theorem unsat9836 : Unsatisfiable (PosFin 65) f9836 := by
  apply lratCheckerSound f9836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9836
  · intro a ha; simp [p9836] at ha; subst a; trivial
  · exact checked9836
theorem derived9836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9836 := by
  apply localUnsat_implies_entails f9836 [c4669, c3820] c9836 unsat9836 (by rfl) a
  have h0 : Entails.eval a c4669 := h 4668 (by decide)
  have h1 : Entails.eval a c3820 := h 3819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9837 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1920, some c1919, some c4536, some c3229, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9837 : lratChecker f9837 p9837 = .success := by decide +kernel
theorem unsat9837 : Unsatisfiable (PosFin 65) f9837 := by
  apply lratCheckerSound f9837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9837
  · intro a ha; simp [p9837] at ha; subst a; trivial
  · exact checked9837
theorem derived9837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9837 := by
  apply localUnsat_implies_entails f9837 [c9748, c1920, c1919, c4536, c3229] c9837 unsat9837 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1920 := h 1919 (by decide)
  have h2 : Entails.eval a c1919 := h 1918 (by decide)
  have h3 : Entails.eval a c4536 := h 4535 (by decide)
  have h4 : Entails.eval a c3229 := h 3228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9838 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c9837, some c1918, some c3226, some c4537, some c3225, some c3228, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p9838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9838 : lratChecker f9838 p9838 = .success := by decide +kernel
theorem unsat9838 : Unsatisfiable (PosFin 65) f9838 := by
  apply lratCheckerSound f9838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9838
  · intro a ha; simp [p9838] at ha; subst a; trivial
  · exact checked9838
theorem derived9838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9838 := by
  apply localUnsat_implies_entails f9838 [c9748, c9837, c1918, c3226, c4537, c3225, c3228] c9838 unsat9838 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c9837 := derived9837 a h
  have h2 : Entails.eval a c1918 := h 1917 (by decide)
  have h3 : Entails.eval a c3226 := h 3225 (by decide)
  have h4 : Entails.eval a c4537 := h 4536 (by decide)
  have h5 : Entails.eval a c3225 := h 3224 (by decide)
  have h6 : Entails.eval a c3228 := h 3227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9839 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c975, some c910, some c909, some c792, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9839 : lratChecker f9839 p9839 = .success := by decide +kernel
theorem unsat9839 : Unsatisfiable (PosFin 65) f9839 := by
  apply lratCheckerSound f9839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9839
  · intro a ha; simp [p9839] at ha; subst a; trivial
  · exact checked9839
theorem derived9839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9839 := by
  apply localUnsat_implies_entails f9839 [c975, c910, c909, c792] c9839 unsat9839 (by rfl) a
  have h0 : Entails.eval a c975 := h 974 (by decide)
  have h1 : Entails.eval a c910 := h 909 (by decide)
  have h2 : Entails.eval a c909 := h 908 (by decide)
  have h3 : Entails.eval a c792 := h 791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9840 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨61, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9833, some c9838, some c2731, some c2759, some c2741, some c9836, some c9839, some c2720, some c2721, some c911, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9840 : lratChecker f9840 p9840 = .success := by decide +kernel
theorem unsat9840 : Unsatisfiable (PosFin 65) f9840 := by
  apply lratCheckerSound f9840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9840
  · intro a ha; simp [p9840] at ha; subst a; trivial
  · exact checked9840
theorem derived9840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9840 := by
  apply localUnsat_implies_entails f9840 [c9833, c9838, c2731, c2759, c2741, c9836, c9839, c2720, c2721, c911] c9840 unsat9840 (by rfl) a
  have h0 : Entails.eval a c9833 := derived9833 a h
  have h1 : Entails.eval a c9838 := derived9838 a h
  have h2 : Entails.eval a c2731 := h 2730 (by decide)
  have h3 : Entails.eval a c2759 := h 2758 (by decide)
  have h4 : Entails.eval a c2741 := h 2740 (by decide)
  have h5 : Entails.eval a c9836 := derived9836 a h
  have h6 : Entails.eval a c9839 := derived9839 a h
  have h7 : Entails.eval a c2720 := h 2719 (by decide)
  have h8 : Entails.eval a c2721 := h 2720 (by decide)
  have h9 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9841 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3212, some c3216, some c3213, some c3221, some c3220, some c1925, some c4539, some c3232, some c1929, some c3219, some c3222, some c1914, some c1915, some c8947, some c3107, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9841 : lratChecker f9841 p9841 = .success := by decide +kernel
theorem unsat9841 : Unsatisfiable (PosFin 65) f9841 := by
  apply lratCheckerSound f9841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9841
  · intro a ha; simp [p9841] at ha; subst a; trivial
  · exact checked9841
theorem derived9841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9841 := by
  apply localUnsat_implies_entails f9841 [c9748, c3212, c3216, c3213, c3221, c3220, c1925, c4539, c3232, c1929, c3219, c3222, c1914, c1915, c8947, c3107] c9841 unsat9841 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3212 := h 3211 (by decide)
  have h2 : Entails.eval a c3216 := h 3215 (by decide)
  have h3 : Entails.eval a c3213 := h 3212 (by decide)
  have h4 : Entails.eval a c3221 := h 3220 (by decide)
  have h5 : Entails.eval a c3220 := h 3219 (by decide)
  have h6 : Entails.eval a c1925 := h 1924 (by decide)
  have h7 : Entails.eval a c4539 := h 4538 (by decide)
  have h8 : Entails.eval a c3232 := h 3231 (by decide)
  have h9 : Entails.eval a c1929 := h 1928 (by decide)
  have h10 : Entails.eval a c3219 := h 3218 (by decide)
  have h11 : Entails.eval a c3222 := h 3221 (by decide)
  have h12 : Entails.eval a c1914 := h 1913 (by decide)
  have h13 : Entails.eval a c1915 := h 1914 (by decide)
  have h14 : Entails.eval a c8947 := derived8947 a h
  have h15 : Entails.eval a c3107 := h 3106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9842 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨56, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8676, some c919, some c978, some c8608, some c2726, some c2725, some c983, some c2716, some c2719, some c804, some c2727, some c772, some c780, some c2717, some c96, some c902, some c767, some c5774, some c6200, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9842 : lratChecker f9842 p9842 = .success := by decide +kernel
theorem unsat9842 : Unsatisfiable (PosFin 65) f9842 := by
  apply lratCheckerSound f9842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9842
  · intro a ha; simp [p9842] at ha; subst a; trivial
  · exact checked9842
theorem derived9842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9842 := by
  apply localUnsat_implies_entails f9842 [c8676, c919, c978, c8608, c2726, c2725, c983, c2716, c2719, c804, c2727, c772, c780, c2717, c96, c902, c767, c5774, c6200] c9842 unsat9842 (by rfl) a
  have h0 : Entails.eval a c8676 := derived8676 a h
  have h1 : Entails.eval a c919 := h 918 (by decide)
  have h2 : Entails.eval a c978 := h 977 (by decide)
  have h3 : Entails.eval a c8608 := derived8608 a h
  have h4 : Entails.eval a c2726 := h 2725 (by decide)
  have h5 : Entails.eval a c2725 := h 2724 (by decide)
  have h6 : Entails.eval a c983 := h 982 (by decide)
  have h7 : Entails.eval a c2716 := h 2715 (by decide)
  have h8 : Entails.eval a c2719 := h 2718 (by decide)
  have h9 : Entails.eval a c804 := h 803 (by decide)
  have h10 : Entails.eval a c2727 := h 2726 (by decide)
  have h11 : Entails.eval a c772 := h 771 (by decide)
  have h12 : Entails.eval a c780 := h 779 (by decide)
  have h13 : Entails.eval a c2717 := h 2716 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c902 := h 901 (by decide)
  have h16 : Entails.eval a c767 := h 766 (by decide)
  have h17 : Entails.eval a c5774 := h 5773 (by decide)
  have h18 : Entails.eval a c6200 := h 6199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9843 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9795, some c9794, some c9832, some c9833, some c9835, some c9840, some c9841, some c2731, some c2759, some c2741, some c9836, some c9842, some c2720, some c2718, some c2721, some c771, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9843 : lratChecker f9843 p9843 = .success := by decide +kernel
theorem unsat9843 : Unsatisfiable (PosFin 65) f9843 := by
  apply lratCheckerSound f9843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9843
  · intro a ha; simp [p9843] at ha; subst a; trivial
  · exact checked9843
theorem derived9843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9843 := by
  apply localUnsat_implies_entails f9843 [c9795, c9794, c9832, c9833, c9835, c9840, c9841, c2731, c2759, c2741, c9836, c9842, c2720, c2718, c2721, c771] c9843 unsat9843 (by rfl) a
  have h0 : Entails.eval a c9795 := derived9795 a h
  have h1 : Entails.eval a c9794 := derived9794 a h
  have h2 : Entails.eval a c9832 := derived9832 a h
  have h3 : Entails.eval a c9833 := derived9833 a h
  have h4 : Entails.eval a c9835 := derived9835 a h
  have h5 : Entails.eval a c9840 := derived9840 a h
  have h6 : Entails.eval a c9841 := derived9841 a h
  have h7 : Entails.eval a c2731 := h 2730 (by decide)
  have h8 : Entails.eval a c2759 := h 2758 (by decide)
  have h9 : Entails.eval a c2741 := h 2740 (by decide)
  have h10 : Entails.eval a c9836 := derived9836 a h
  have h11 : Entails.eval a c9842 := derived9842 a h
  have h12 : Entails.eval a c2720 := h 2719 (by decide)
  have h13 : Entails.eval a c2718 := h 2717 (by decide)
  have h14 : Entails.eval a c2721 := h 2720 (by decide)
  have h15 : Entails.eval a c771 := h 770 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9844 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4627, some c9799, some c4635, some c4622, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9844 : lratChecker f9844 p9844 = .success := by decide +kernel
theorem unsat9844 : Unsatisfiable (PosFin 65) f9844 := by
  apply lratCheckerSound f9844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9844
  · intro a ha; simp [p9844] at ha; subst a; trivial
  · exact checked9844
theorem derived9844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9844 := by
  apply localUnsat_implies_entails f9844 [c4627, c9799, c4635, c4622] c9844 unsat9844 (by rfl) a
  have h0 : Entails.eval a c4627 := h 4626 (by decide)
  have h1 : Entails.eval a c9799 := derived9799 a h
  have h2 : Entails.eval a c4635 := h 4634 (by decide)
  have h3 : Entails.eval a c4622 := h 4621 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9845 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨12, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9800, some c9452, some c2740, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9845 : lratChecker f9845 p9845 = .success := by decide +kernel
theorem unsat9845 : Unsatisfiable (PosFin 65) f9845 := by
  apply lratCheckerSound f9845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9845
  · intro a ha; simp [p9845] at ha; subst a; trivial
  · exact checked9845
theorem derived9845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9845 := by
  apply localUnsat_implies_entails f9845 [c9800, c9452, c2740] c9845 unsat9845 (by rfl) a
  have h0 : Entails.eval a c9800 := derived9800 a h
  have h1 : Entails.eval a c9452 := derived9452 a h
  have h2 : Entails.eval a c2740 := h 2739 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9846 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨57, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1939, some c1950, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9846 : lratChecker f9846 p9846 = .success := by decide +kernel
theorem unsat9846 : Unsatisfiable (PosFin 65) f9846 := by
  apply lratCheckerSound f9846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9846
  · intro a ha; simp [p9846] at ha; subst a; trivial
  · exact checked9846
theorem derived9846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9846 := by
  apply localUnsat_implies_entails f9846 [c9748, c1939, c1950] c9846 unsat9846 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1939 := h 1938 (by decide)
  have h2 : Entails.eval a c1950 := h 1949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9847 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨64, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9830, some c9792, some c9794, some c9795, some c9831, some c9843, some c9844, some c9845, some c9846, some c2746, some c3339, some c3812, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9847 : lratChecker f9847 p9847 = .success := by decide +kernel
theorem unsat9847 : Unsatisfiable (PosFin 65) f9847 := by
  apply lratCheckerSound f9847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9847
  · intro a ha; simp [p9847] at ha; subst a; trivial
  · exact checked9847
theorem derived9847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9847 := by
  apply localUnsat_implies_entails f9847 [c9830, c9792, c9794, c9795, c9831, c9843, c9844, c9845, c9846, c2746, c3339, c3812] c9847 unsat9847 (by rfl) a
  have h0 : Entails.eval a c9830 := derived9830 a h
  have h1 : Entails.eval a c9792 := derived9792 a h
  have h2 : Entails.eval a c9794 := derived9794 a h
  have h3 : Entails.eval a c9795 := derived9795 a h
  have h4 : Entails.eval a c9831 := derived9831 a h
  have h5 : Entails.eval a c9843 := derived9843 a h
  have h6 : Entails.eval a c9844 := derived9844 a h
  have h7 : Entails.eval a c9845 := derived9845 a h
  have h8 : Entails.eval a c9846 := derived9846 a h
  have h9 : Entails.eval a c2746 := h 2745 (by decide)
  have h10 : Entails.eval a c3339 := h 3338 (by decide)
  have h11 : Entails.eval a c3812 := h 3811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9848 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3560, some c882, some c895, some c890, some c3229, some c3227, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9848 : lratChecker f9848 p9848 = .success := by decide +kernel
theorem unsat9848 : Unsatisfiable (PosFin 65) f9848 := by
  apply lratCheckerSound f9848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9848
  · intro a ha; simp [p9848] at ha; subst a; trivial
  · exact checked9848
theorem derived9848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9848 := by
  apply localUnsat_implies_entails f9848 [c3560, c882, c895, c890, c3229, c3227] c9848 unsat9848 (by rfl) a
  have h0 : Entails.eval a c3560 := h 3559 (by decide)
  have h1 : Entails.eval a c882 := h 881 (by decide)
  have h2 : Entails.eval a c895 := h 894 (by decide)
  have h3 : Entails.eval a c890 := h 889 (by decide)
  have h4 : Entails.eval a c3229 := h 3228 (by decide)
  have h5 : Entails.eval a c3227 := h 3226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9849 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨59, by decide⟩, true), (⟨60, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3266, some c9848, some c3554, some c883, some c3224, some c3225, some c3228, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9849 : lratChecker f9849 p9849 = .success := by decide +kernel
theorem unsat9849 : Unsatisfiable (PosFin 65) f9849 := by
  apply lratCheckerSound f9849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9849
  · intro a ha; simp [p9849] at ha; subst a; trivial
  · exact checked9849
theorem derived9849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9849 := by
  apply localUnsat_implies_entails f9849 [c3266, c9848, c3554, c883, c3224, c3225, c3228] c9849 unsat9849 (by rfl) a
  have h0 : Entails.eval a c3266 := h 3265 (by decide)
  have h1 : Entails.eval a c9848 := derived9848 a h
  have h2 : Entails.eval a c3554 := h 3553 (by decide)
  have h3 : Entails.eval a c883 := h 882 (by decide)
  have h4 : Entails.eval a c3224 := h 3223 (by decide)
  have h5 : Entails.eval a c3225 := h 3224 (by decide)
  have h6 : Entails.eval a c3228 := h 3227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9850 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3560, some c909, some c807, some c890, some c792, some c788, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p9850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9850 : lratChecker f9850 p9850 = .success := by decide +kernel
theorem unsat9850 : Unsatisfiable (PosFin 65) f9850 := by
  apply lratCheckerSound f9850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9850
  · intro a ha; simp [p9850] at ha; subst a; trivial
  · exact checked9850
theorem derived9850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9850 := by
  apply localUnsat_implies_entails f9850 [c3560, c909, c807, c890, c792, c788] c9850 unsat9850 (by rfl) a
  have h0 : Entails.eval a c3560 := h 3559 (by decide)
  have h1 : Entails.eval a c909 := h 908 (by decide)
  have h2 : Entails.eval a c807 := h 806 (by decide)
  have h3 : Entails.eval a c890 := h 889 (by decide)
  have h4 : Entails.eval a c792 := h 791 (by decide)
  have h5 : Entails.eval a c788 := h 787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9850

end CochromaticTwenty.Certificates.FixedCore0
