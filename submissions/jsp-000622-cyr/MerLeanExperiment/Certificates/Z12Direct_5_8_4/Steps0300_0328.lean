import MerLeanExperiment.Certificates.Z12Direct_5_8_4.Steps0200_0299

/-! Generated from the actual pinned z12direct_5_8_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c831 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c300, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p831 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 31) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c746, c300] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c832 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c320, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p832 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 31) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c667, c320] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c833 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c796, some c346, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p833 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 31) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c667, c796, c346] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c796, some c381, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p834 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 31) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c746, c796, c381] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c796, some c404, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p835 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 31) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c746, c796, c404] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c404 := h 403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c746, some c405, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p836 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 31) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c746, c405] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c837 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c410, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p837 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 31) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c667, c410] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c838 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c412, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p838 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 31) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c796, c412] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c412 := h 411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c839 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c796, some c436, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p839 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 31) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c667, c796, c436] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c436 := h 435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c667, some c796, some c439, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p840 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 31) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c667, c796, c439] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c796 := derived796 a h
  have h2 : Entails.eval a c439 := h 438 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c796, some c727, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p841 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 31) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c796, c727] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c796 := derived796 a h
  have h1 : Entails.eval a c727 := derived727 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c842 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨26, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c803, some c821, some c68, some c66, some c818, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p842 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 31) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c803, c821, c68, c66, c818] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c803 := derived803 a h
  have h1 : Entails.eval a c821 := derived821 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c813, some c804, some c842, some c55, some c245, some c827, some c816, some c828, some c48, some c180, some c429, some c466, some c86, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p843 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 31) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c813, c804, c842, c55, c245, c827, c816, c828, c48, c180, c429, c466, c86] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c813 := derived813 a h
  have h1 : Entails.eval a c804 := derived804 a h
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c827 := derived827 a h
  have h6 : Entails.eval a c816 := derived816 a h
  have h7 : Entails.eval a c828 := derived828 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c429 := h 428 (by decide)
  have h11 : Entails.eval a c466 := h 465 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c843, some c813, some c804, some c801, some c55, some c245, some c830, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p844 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 31) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c843, c813, c804, c801, c55, c245, c830] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c804 := derived804 a h
  have h3 : Entails.eval a c801 := derived801 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c844, some c813, some c804, some c55, some c245, some c827, some c828, some c817, some c48, some c180, some c375, some c338, some c86, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p845 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 31) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c844, c813, c804, c55, c245, c827, c828, c817, c48, c180, c375, c338, c86] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c844 := derived844 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c804 := derived804 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c827 := derived827 a h
  have h6 : Entails.eval a c828 := derived828 a h
  have h7 : Entails.eval a c817 := derived817 a h
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c804, some c843, some c844, some c845, some c819, some c834, some c838, some c148, some c828, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p846 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 31) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c804, c843, c844, c845, c819, c834, c838, c148, c828] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c804 := derived804 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c844 := derived844 a h
  have h3 : Entails.eval a c845 := derived845 a h
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c834 := derived834 a h
  have h6 : Entails.eval a c838 := derived838 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c828 := derived828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c678, some c711, some c818, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p847 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 31) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c846, c678, c711, c818] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c678 := derived678 a h
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c827, some c823, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p848 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 31) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c846, c827, c823] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c827 := derived827 a h
  have h2 : Entails.eval a c823 := derived823 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c848, some c818, some c847, some c115, some c589, some c836, some c446, some c841, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p849 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 31) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c848, c818, c847, c115, c589, c836, c446, c841] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c847 := derived847 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c836 := derived836 a h
  have h6 : Entails.eval a c446 := h 445 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c847, some c849, some c686, some c818, some c825, some c815, some c39, some c546, some c403, some c231, some c829, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p850 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 31) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c846, c847, c849, c686, c818, c825, c815, c39, c546, c403, c231, c829] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c849 := derived849 a h
  have h3 : Entails.eval a c686 := derived686 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c825 := derived825 a h
  have h6 : Entails.eval a c815 := derived815 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c546 := derived546 a h
  have h9 : Entails.eval a c403 := h 402 (by decide)
  have h10 : Entails.eval a c231 := h 230 (by decide)
  have h11 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c847, some c818, some c849, some c686, some c850, some c32, some c837, some c832, some c209, some c293, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p851 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 31) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c846, c847, c818, c849, c686, c850, c32, c837, c832, c209, c293] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c686 := derived686 a h
  have h5 : Entails.eval a c850 := derived850 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c837 := derived837 a h
  have h8 : Entails.eval a c832 := derived832 a h
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c848, some c846, some c851, some c67, some c847, some c682, some c824, some c137, some c822, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p852 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 31) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c848, c846, c851, c67, c847, c682, c824, c137, c822] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c851 := derived851 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c847 := derived847 a h
  have h5 : Entails.eval a c682 := derived682 a h
  have h6 : Entails.eval a c824 := derived824 a h
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c822 := derived822 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c848, some c32, some c851, some c67, some c847, some c682, some c824, some c242, some c683, some c852, some c293, some c136, some c820, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p853 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 31) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c846, c848, c32, c851, c67, c847, c682, c824, c242, c683, c852, c293, c136, c820] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c848 := derived848 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c851 := derived851 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c682 := derived682 a h
  have h7 : Entails.eval a c824 := derived824 a h
  have h8 : Entails.eval a c242 := h 241 (by decide)
  have h9 : Entails.eval a c683 := derived683 a h
  have h10 : Entails.eval a c852 := derived852 a h
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c848, some c814, some c686, some c115, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p854 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 31) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c846, c848, c814, c686, c115] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c848 := derived848 a h
  have h2 : Entails.eval a c814 := derived814 a h
  have h3 : Entails.eval a c686 := derived686 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c848, some c846, some c851, some c824, some c67, some c847, some c682, some c854, some c683, some c853, some c852, some c839, some c138, some c820, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p855 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 31) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c848, c846, c851, c824, c67, c847, c682, c854, c683, c853, c852, c839, c138, c820] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c846 := derived846 a h
  have h2 : Entails.eval a c851 := derived851 a h
  have h3 : Entails.eval a c824 := derived824 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c682 := derived682 a h
  have h7 : Entails.eval a c854 := derived854 a h
  have h8 : Entails.eval a c683 := derived683 a h
  have h9 : Entails.eval a c853 := derived853 a h
  have h10 : Entails.eval a c852 := derived852 a h
  have h11 : Entails.eval a c839 := derived839 a h
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c855, some c851, some c824, some c67, some c847, some c839, some c815, some c833, some c11, some c840, some c39, some c546, some c279, some c831, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p856 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 31) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c846, c855, c851, c824, c67, c847, c839, c815, c833, c11, c840, c39, c546, c279, c831] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c851 := derived851 a h
  have h3 : Entails.eval a c824 := derived824 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c839 := derived839 a h
  have h7 : Entails.eval a c815 := derived815 a h
  have h8 : Entails.eval a c833 := derived833 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c840 := derived840 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c546 := derived546 a h
  have h13 : Entails.eval a c279 := h 278 (by decide)
  have h14 : Entails.eval a c831 := derived831 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c846, some c847, some c851, some c67, some c824, some c855, some c14, some c856, some c220, some c130, some c135, some c59, some c401, some c835, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p857 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 31) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c846, c847, c851, c67, c824, c855, c14, c856, c220, c130, c135, c59, c401, c835] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c846 := derived846 a h
  have h1 : Entails.eval a c847 := derived847 a h
  have h2 : Entails.eval a c851 := derived851 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c824 := derived824 a h
  have h5 : Entails.eval a c855 := derived855 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c856 := derived856 a h
  have h8 : Entails.eval a c220 := h 219 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c401 := h 400 (by decide)
  have h13 : Entails.eval a c835 := derived835 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c848, some c857, some c826, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p858 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 31) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c848, c857, c826] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c826 := derived826 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c848, some c858, some c846, some c857, some c95]
def p859 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 31) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c848, c858, c846, c857, c95] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c848 := derived848 a h
  have h1 : Entails.eval a c858 := derived858 a h
  have h2 : Entails.eval a c846 := derived846 a h
  have h3 : Entails.eval a c857 := derived857 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived859

end CochromaticTwenty.Certificates.Z12Direct_5_8_4
