import MerLeanExperiment.Certificates.FixedCore0.Steps2900_2999

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10551 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨6, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1826, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10551 : lratChecker f10551 p10551 = .success := by decide +kernel
theorem unsat10551 : Unsatisfiable (PosFin 65) f10551 := by
  apply lratCheckerSound f10551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10551
  · intro a ha; simp [p10551] at ha; subst a; trivial
  · exact checked10551
theorem derived10551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10551 := by
  apply localUnsat_implies_entails f10551 [c9748, c1826] c10551 unsat10551 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1826 := h 1825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10552 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1832, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10552 : lratChecker f10552 p10552 = .success := by decide +kernel
theorem unsat10552 : Unsatisfiable (PosFin 65) f10552 := by
  apply lratCheckerSound f10552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10552
  · intro a ha; simp [p10552] at ha; subst a; trivial
  · exact checked10552
theorem derived10552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10552 := by
  apply localUnsat_implies_entails f10552 [c9748, c1832] c10552 unsat10552 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1832 := h 1831 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10553 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1849, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p10553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10553 : lratChecker f10553 p10553 = .success := by decide +kernel
theorem unsat10553 : Unsatisfiable (PosFin 65) f10553 := by
  apply lratCheckerSound f10553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10553
  · intro a ha; simp [p10553] at ha; subst a; trivial
  · exact checked10553
theorem derived10553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10553 := by
  apply localUnsat_implies_entails f10553 [c9748, c1849] c10553 unsat10553 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1849 := h 1848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10554 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨59, by decide⟩, false), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1602, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10554 : lratChecker f10554 p10554 = .success := by decide +kernel
theorem unsat10554 : Unsatisfiable (PosFin 65) f10554 := by
  apply lratCheckerSound f10554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10554
  · intro a ha; simp [p10554] at ha; subst a; trivial
  · exact checked10554
theorem derived10554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10554 := by
  apply localUnsat_implies_entails f10554 [c9748, c1602] c10554 unsat10554 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1602 := h 1601 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10555 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1627, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p10555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10555 : lratChecker f10555 p10555 = .success := by decide +kernel
theorem unsat10555 : Unsatisfiable (PosFin 65) f10555 := by
  apply lratCheckerSound f10555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10555
  · intro a ha; simp [p10555] at ha; subst a; trivial
  · exact checked10555
theorem derived10555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10555 := by
  apply localUnsat_implies_entails f10555 [c9748, c1627] c10555 unsat10555 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1627 := h 1626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10556 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1600, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10556 : lratChecker f10556 p10556 = .success := by decide +kernel
theorem unsat10556 : Unsatisfiable (PosFin 65) f10556 := by
  apply lratCheckerSound f10556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10556
  · intro a ha; simp [p10556] at ha; subst a; trivial
  · exact checked10556
theorem derived10556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10556 := by
  apply localUnsat_implies_entails f10556 [c9748, c1600] c10556 unsat10556 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1600 := h 1599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10557 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1636, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p10557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10557 : lratChecker f10557 p10557 = .success := by decide +kernel
theorem unsat10557 : Unsatisfiable (PosFin 65) f10557 := by
  apply lratCheckerSound f10557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10557
  · intro a ha; simp [p10557] at ha; subst a; trivial
  · exact checked10557
theorem derived10557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10557 := by
  apply localUnsat_implies_entails f10557 [c9748, c1636] c10557 unsat10557 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1636 := h 1635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10558 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2318, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10558 : lratChecker f10558 p10558 = .success := by decide +kernel
theorem unsat10558 : Unsatisfiable (PosFin 65) f10558 := by
  apply lratCheckerSound f10558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10558
  · intro a ha; simp [p10558] at ha; subst a; trivial
  · exact checked10558
theorem derived10558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10558 := by
  apply localUnsat_implies_entails f10558 [c9748, c2318] c10558 unsat10558 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2318 := h 2317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10559 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, false), (⟨13, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2319, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10559 : lratChecker f10559 p10559 = .success := by decide +kernel
theorem unsat10559 : Unsatisfiable (PosFin 65) f10559 := by
  apply lratCheckerSound f10559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10559
  · intro a ha; simp [p10559] at ha; subst a; trivial
  · exact checked10559
theorem derived10559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10559 := by
  apply localUnsat_implies_entails f10559 [c9748, c2319] c10559 unsat10559 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2319 := h 2318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10560 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2321, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10560 : lratChecker f10560 p10560 = .success := by decide +kernel
theorem unsat10560 : Unsatisfiable (PosFin 65) f10560 := by
  apply lratCheckerSound f10560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10560
  · intro a ha; simp [p10560] at ha; subst a; trivial
  · exact checked10560
theorem derived10560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10560 := by
  apply localUnsat_implies_entails f10560 [c9748, c2321] c10560 unsat10560 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2321 := h 2320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10561 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1611, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10561 : lratChecker f10561 p10561 = .success := by decide +kernel
theorem unsat10561 : Unsatisfiable (PosFin 65) f10561 := by
  apply lratCheckerSound f10561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10561
  · intro a ha; simp [p10561] at ha; subst a; trivial
  · exact checked10561
theorem derived10561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10561 := by
  apply localUnsat_implies_entails f10561 [c9748, c1611] c10561 unsat10561 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1611 := h 1610 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10562 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1620, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10562 : lratChecker f10562 p10562 = .success := by decide +kernel
theorem unsat10562 : Unsatisfiable (PosFin 65) f10562 := by
  apply lratCheckerSound f10562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10562
  · intro a ha; simp [p10562] at ha; subst a; trivial
  · exact checked10562
theorem derived10562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10562 := by
  apply localUnsat_implies_entails f10562 [c9748, c1620] c10562 unsat10562 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1620 := h 1619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10563 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1596, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10563 : lratChecker f10563 p10563 = .success := by decide +kernel
theorem unsat10563 : Unsatisfiable (PosFin 65) f10563 := by
  apply lratCheckerSound f10563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10563
  · intro a ha; simp [p10563] at ha; subst a; trivial
  · exact checked10563
theorem derived10563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10563 := by
  apply localUnsat_implies_entails f10563 [c9748, c1596] c10563 unsat10563 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1596 := h 1595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10564 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1828, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10564 : lratChecker f10564 p10564 = .success := by decide +kernel
theorem unsat10564 : Unsatisfiable (PosFin 65) f10564 := by
  apply lratCheckerSound f10564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10564
  · intro a ha; simp [p10564] at ha; subst a; trivial
  · exact checked10564
theorem derived10564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10564 := by
  apply localUnsat_implies_entails f10564 [c9748, c1828] c10564 unsat10564 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1828 := h 1827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10565 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2273, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10565 : lratChecker f10565 p10565 = .success := by decide +kernel
theorem unsat10565 : Unsatisfiable (PosFin 65) f10565 := by
  apply lratCheckerSound f10565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10565
  · intro a ha; simp [p10565] at ha; subst a; trivial
  · exact checked10565
theorem derived10565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10565 := by
  apply localUnsat_implies_entails f10565 [c9748, c2273] c10565 unsat10565 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2273 := h 2272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10566 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1660, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10566 : lratChecker f10566 p10566 = .success := by decide +kernel
theorem unsat10566 : Unsatisfiable (PosFin 65) f10566 := by
  apply lratCheckerSound f10566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10566
  · intro a ha; simp [p10566] at ha; subst a; trivial
  · exact checked10566
theorem derived10566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10566 := by
  apply localUnsat_implies_entails f10566 [c9748, c1660] c10566 unsat10566 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1660 := h 1659 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10567 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨63, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1662, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10567 : lratChecker f10567 p10567 = .success := by decide +kernel
theorem unsat10567 : Unsatisfiable (PosFin 65) f10567 := by
  apply lratCheckerSound f10567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10567
  · intro a ha; simp [p10567] at ha; subst a; trivial
  · exact checked10567
theorem derived10567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10567 := by
  apply localUnsat_implies_entails f10567 [c9748, c1662] c10567 unsat10567 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1662 := h 1661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10568 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1893, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10568 : lratChecker f10568 p10568 = .success := by decide +kernel
theorem unsat10568 : Unsatisfiable (PosFin 65) f10568 := by
  apply lratCheckerSound f10568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10568
  · intro a ha; simp [p10568] at ha; subst a; trivial
  · exact checked10568
theorem derived10568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10568 := by
  apply localUnsat_implies_entails f10568 [c9748, c1893] c10568 unsat10568 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1893 := h 1892 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10569 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1907, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10569 : lratChecker f10569 p10569 = .success := by decide +kernel
theorem unsat10569 : Unsatisfiable (PosFin 65) f10569 := by
  apply lratCheckerSound f10569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10569
  · intro a ha; simp [p10569] at ha; subst a; trivial
  · exact checked10569
theorem derived10569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10569 := by
  apply localUnsat_implies_entails f10569 [c9748, c1907] c10569 unsat10569 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1907 := h 1906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10570 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨62, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1653, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, false))]
def p10570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10570 : lratChecker f10570 p10570 = .success := by decide +kernel
theorem unsat10570 : Unsatisfiable (PosFin 65) f10570 := by
  apply lratCheckerSound f10570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10570
  · intro a ha; simp [p10570] at ha; subst a; trivial
  · exact checked10570
theorem derived10570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10570 := by
  apply localUnsat_implies_entails f10570 [c9748, c1653] c10570 unsat10570 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1653 := h 1652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10571 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1837, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10571 : lratChecker f10571 p10571 = .success := by decide +kernel
theorem unsat10571 : Unsatisfiable (PosFin 65) f10571 := by
  apply lratCheckerSound f10571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10571
  · intro a ha; simp [p10571] at ha; subst a; trivial
  · exact checked10571
theorem derived10571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10571 := by
  apply localUnsat_implies_entails f10571 [c9748, c1837] c10571 unsat10571 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1837 := h 1836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10572 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1829, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10572 : lratChecker f10572 p10572 = .success := by decide +kernel
theorem unsat10572 : Unsatisfiable (PosFin 65) f10572 := by
  apply lratCheckerSound f10572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10572
  · intro a ha; simp [p10572] at ha; subst a; trivial
  · exact checked10572
theorem derived10572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10572 := by
  apply localUnsat_implies_entails f10572 [c9748, c1829] c10572 unsat10572 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1829 := h 1828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10573 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨61, by decide⟩, true), (⟨5, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1650, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10573 : lratChecker f10573 p10573 = .success := by decide +kernel
theorem unsat10573 : Unsatisfiable (PosFin 65) f10573 := by
  apply lratCheckerSound f10573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10573
  · intro a ha; simp [p10573] at ha; subst a; trivial
  · exact checked10573
theorem derived10573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10573 := by
  apply localUnsat_implies_entails f10573 [c9748, c1650] c10573 unsat10573 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1650 := h 1649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10574 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨57, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1605, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10574 : lratChecker f10574 p10574 = .success := by decide +kernel
theorem unsat10574 : Unsatisfiable (PosFin 65) f10574 := by
  apply lratCheckerSound f10574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10574
  · intro a ha; simp [p10574] at ha; subst a; trivial
  · exact checked10574
theorem derived10574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10574 := by
  apply localUnsat_implies_entails f10574 [c9748, c1605] c10574 unsat10574 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1605 := h 1604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10575 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨57, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1904, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10575 : lratChecker f10575 p10575 = .success := by decide +kernel
theorem unsat10575 : Unsatisfiable (PosFin 65) f10575 := by
  apply lratCheckerSound f10575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10575
  · intro a ha; simp [p10575] at ha; subst a; trivial
  · exact checked10575
theorem derived10575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10575 := by
  apply localUnsat_implies_entails f10575 [c9748, c1904] c10575 unsat10575 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1904 := h 1903 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10576 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨58, by decide⟩, true), (⟨56, by decide⟩, true), (⟨16, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1909, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10576 : lratChecker f10576 p10576 = .success := by decide +kernel
theorem unsat10576 : Unsatisfiable (PosFin 65) f10576 := by
  apply lratCheckerSound f10576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10576
  · intro a ha; simp [p10576] at ha; subst a; trivial
  · exact checked10576
theorem derived10576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10576 := by
  apply localUnsat_implies_entails f10576 [c9748, c1909] c10576 unsat10576 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1909 := h 1908 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10577 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1658, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10577 : lratChecker f10577 p10577 = .success := by decide +kernel
theorem unsat10577 : Unsatisfiable (PosFin 65) f10577 := by
  apply lratCheckerSound f10577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10577
  · intro a ha; simp [p10577] at ha; subst a; trivial
  · exact checked10577
theorem derived10577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10577 := by
  apply localUnsat_implies_entails f10577 [c9748, c1658] c10577 unsat10577 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1658 := h 1657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10578 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2325, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10578 : lratChecker f10578 p10578 = .success := by decide +kernel
theorem unsat10578 : Unsatisfiable (PosFin 65) f10578 := by
  apply lratCheckerSound f10578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10578
  · intro a ha; simp [p10578] at ha; subst a; trivial
  · exact checked10578
theorem derived10578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10578 := by
  apply localUnsat_implies_entails f10578 [c9748, c2325] c10578 unsat10578 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2325 := h 2324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10579 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1648, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10579 : lratChecker f10579 p10579 = .success := by decide +kernel
theorem unsat10579 : Unsatisfiable (PosFin 65) f10579 := by
  apply lratCheckerSound f10579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10579
  · intro a ha; simp [p10579] at ha; subst a; trivial
  · exact checked10579
theorem derived10579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10579 := by
  apply localUnsat_implies_entails f10579 [c9748, c1648] c10579 unsat10579 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1648 := h 1647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10580 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1891, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10580 : lratChecker f10580 p10580 = .success := by decide +kernel
theorem unsat10580 : Unsatisfiable (PosFin 65) f10580 := by
  apply lratCheckerSound f10580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10580
  · intro a ha; simp [p10580] at ha; subst a; trivial
  · exact checked10580
theorem derived10580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10580 := by
  apply localUnsat_implies_entails f10580 [c9748, c1891] c10580 unsat10580 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1891 := h 1890 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10581 : DefaultClause 65 := directClause [(⟨39, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1871, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10581 : lratChecker f10581 p10581 = .success := by decide +kernel
theorem unsat10581 : Unsatisfiable (PosFin 65) f10581 := by
  apply lratCheckerSound f10581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10581
  · intro a ha; simp [p10581] at ha; subst a; trivial
  · exact checked10581
theorem derived10581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10581 := by
  apply localUnsat_implies_entails f10581 [c9748, c1871] c10581 unsat10581 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1871 := h 1870 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10582 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1895, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10582 : lratChecker f10582 p10582 = .success := by decide +kernel
theorem unsat10582 : Unsatisfiable (PosFin 65) f10582 := by
  apply lratCheckerSound f10582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10582
  · intro a ha; simp [p10582] at ha; subst a; trivial
  · exact checked10582
theorem derived10582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10582 := by
  apply localUnsat_implies_entails f10582 [c9748, c1895] c10582 unsat10582 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1895 := h 1894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10583 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1896, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10583 : lratChecker f10583 p10583 = .success := by decide +kernel
theorem unsat10583 : Unsatisfiable (PosFin 65) f10583 := by
  apply lratCheckerSound f10583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10583
  · intro a ha; simp [p10583] at ha; subst a; trivial
  · exact checked10583
theorem derived10583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10583 := by
  apply localUnsat_implies_entails f10583 [c9748, c1896] c10583 unsat10583 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1896 := h 1895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10584 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1831, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10584 : lratChecker f10584 p10584 = .success := by decide +kernel
theorem unsat10584 : Unsatisfiable (PosFin 65) f10584 := by
  apply lratCheckerSound f10584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10584
  · intro a ha; simp [p10584] at ha; subst a; trivial
  · exact checked10584
theorem derived10584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10584 := by
  apply localUnsat_implies_entails f10584 [c9748, c1831] c10584 unsat10584 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1831 := h 1830 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10585 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1823, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p10585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10585 : lratChecker f10585 p10585 = .success := by decide +kernel
theorem unsat10585 : Unsatisfiable (PosFin 65) f10585 := by
  apply lratCheckerSound f10585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10585
  · intro a ha; simp [p10585] at ha; subst a; trivial
  · exact checked10585
theorem derived10585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10585 := by
  apply localUnsat_implies_entails f10585 [c9748, c1823] c10585 unsat10585 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1823 := h 1822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10586 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨6, by decide⟩, true), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1911, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p10586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10586 : lratChecker f10586 p10586 = .success := by decide +kernel
theorem unsat10586 : Unsatisfiable (PosFin 65) f10586 := by
  apply lratCheckerSound f10586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10586
  · intro a ha; simp [p10586] at ha; subst a; trivial
  · exact checked10586
theorem derived10586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10586 := by
  apply localUnsat_implies_entails f10586 [c9748, c1911] c10586 unsat10586 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1911 := h 1910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10587 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1888, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10587 : lratChecker f10587 p10587 = .success := by decide +kernel
theorem unsat10587 : Unsatisfiable (PosFin 65) f10587 := by
  apply lratCheckerSound f10587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10587
  · intro a ha; simp [p10587] at ha; subst a; trivial
  · exact checked10587
theorem derived10587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10587 := by
  apply localUnsat_implies_entails f10587 [c9748, c1888] c10587 unsat10587 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1888 := h 1887 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10588 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1641, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10588 : lratChecker f10588 p10588 = .success := by decide +kernel
theorem unsat10588 : Unsatisfiable (PosFin 65) f10588 := by
  apply lratCheckerSound f10588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10588
  · intro a ha; simp [p10588] at ha; subst a; trivial
  · exact checked10588
theorem derived10588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10588 := by
  apply localUnsat_implies_entails f10588 [c9748, c1641] c10588 unsat10588 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1641 := h 1640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10589 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, true), (⟨61, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1882, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false))]
def p10589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10589 : lratChecker f10589 p10589 = .success := by decide +kernel
theorem unsat10589 : Unsatisfiable (PosFin 65) f10589 := by
  apply lratCheckerSound f10589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10589
  · intro a ha; simp [p10589] at ha; subst a; trivial
  · exact checked10589
theorem derived10589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10589 := by
  apply localUnsat_implies_entails f10589 [c9748, c1882] c10589 unsat10589 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1882 := h 1881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10590 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨63, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1901, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false))]
def p10590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10590 : lratChecker f10590 p10590 = .success := by decide +kernel
theorem unsat10590 : Unsatisfiable (PosFin 65) f10590 := by
  apply lratCheckerSound f10590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10590
  · intro a ha; simp [p10590] at ha; subst a; trivial
  · exact checked10590
theorem derived10590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10590 := by
  apply localUnsat_implies_entails f10590 [c9748, c1901] c10590 unsat10590 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1901 := h 1900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10591 : DefaultClause 65 := directClause [(⟨56, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨16, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1903, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10591 : lratChecker f10591 p10591 = .success := by decide +kernel
theorem unsat10591 : Unsatisfiable (PosFin 65) f10591 := by
  apply lratCheckerSound f10591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10591
  · intro a ha; simp [p10591] at ha; subst a; trivial
  · exact checked10591
theorem derived10591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10591 := by
  apply localUnsat_implies_entails f10591 [c9748, c1903] c10591 unsat10591 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1903 := h 1902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10592 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨58, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1898, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10592 : lratChecker f10592 p10592 = .success := by decide +kernel
theorem unsat10592 : Unsatisfiable (PosFin 65) f10592 := by
  apply lratCheckerSound f10592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10592
  · intro a ha; simp [p10592] at ha; subst a; trivial
  · exact checked10592
theorem derived10592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10592 := by
  apply localUnsat_implies_entails f10592 [c9748, c1898] c10592 unsat10592 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1898 := h 1897 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10593 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1868, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p10593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10593 : lratChecker f10593 p10593 = .success := by decide +kernel
theorem unsat10593 : Unsatisfiable (PosFin 65) f10593 := by
  apply lratCheckerSound f10593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10593
  · intro a ha; simp [p10593] at ha; subst a; trivial
  · exact checked10593
theorem derived10593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10593 := by
  apply localUnsat_implies_entails f10593 [c9748, c1868] c10593 unsat10593 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1868 := h 1867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10594 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1860, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p10594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10594 : lratChecker f10594 p10594 = .success := by decide +kernel
theorem unsat10594 : Unsatisfiable (PosFin 65) f10594 := by
  apply lratCheckerSound f10594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10594
  · intro a ha; simp [p10594] at ha; subst a; trivial
  · exact checked10594
theorem derived10594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10594 := by
  apply localUnsat_implies_entails f10594 [c9748, c1860] c10594 unsat10594 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1860 := h 1859 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10595 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1825, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10595 : lratChecker f10595 p10595 = .success := by decide +kernel
theorem unsat10595 : Unsatisfiable (PosFin 65) f10595 := by
  apply lratCheckerSound f10595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10595
  · intro a ha; simp [p10595] at ha; subst a; trivial
  · exact checked10595
theorem derived10595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10595 := by
  apply localUnsat_implies_entails f10595 [c9748, c1825] c10595 unsat10595 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1825 := h 1824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10596 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1847, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10596 : lratChecker f10596 p10596 = .success := by decide +kernel
theorem unsat10596 : Unsatisfiable (PosFin 65) f10596 := by
  apply lratCheckerSound f10596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10596
  · intro a ha; simp [p10596] at ha; subst a; trivial
  · exact checked10596
theorem derived10596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10596 := by
  apply localUnsat_implies_entails f10596 [c9748, c1847] c10596 unsat10596 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1847 := h 1846 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10597 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1862, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10597 : lratChecker f10597 p10597 = .success := by decide +kernel
theorem unsat10597 : Unsatisfiable (PosFin 65) f10597 := by
  apply lratCheckerSound f10597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10597
  · intro a ha; simp [p10597] at ha; subst a; trivial
  · exact checked10597
theorem derived10597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10597 := by
  apply localUnsat_implies_entails f10597 [c9748, c1862] c10597 unsat10597 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1862 := h 1861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10598 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1854, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10598 : lratChecker f10598 p10598 = .success := by decide +kernel
theorem unsat10598 : Unsatisfiable (PosFin 65) f10598 := by
  apply lratCheckerSound f10598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10598
  · intro a ha; simp [p10598] at ha; subst a; trivial
  · exact checked10598
theorem derived10598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10598 := by
  apply localUnsat_implies_entails f10598 [c9748, c1854] c10598 unsat10598 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1854 := h 1853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10599 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨6, by decide⟩, true), (⟨61, by decide⟩, false), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1900, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10599 : lratChecker f10599 p10599 = .success := by decide +kernel
theorem unsat10599 : Unsatisfiable (PosFin 65) f10599 := by
  apply lratCheckerSound f10599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10599
  · intro a ha; simp [p10599] at ha; subst a; trivial
  · exact checked10599
theorem derived10599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10599 := by
  apply localUnsat_implies_entails f10599 [c9748, c1900] c10599 unsat10599 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1900 := h 1899 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10600 : DefaultClause 65 := directClause [(⟨43, by decide⟩, true), (⟨34, by decide⟩, true), (⟨16, by decide⟩, true), (⟨46, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2316, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10600 : lratChecker f10600 p10600 = .success := by decide +kernel
theorem unsat10600 : Unsatisfiable (PosFin 65) f10600 := by
  apply lratCheckerSound f10600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10600
  · intro a ha; simp [p10600] at ha; subst a; trivial
  · exact checked10600
theorem derived10600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10600 := by
  apply localUnsat_implies_entails f10600 [c9748, c2316] c10600 unsat10600 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2316 := h 2315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10601 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2322, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p10601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10601 : lratChecker f10601 p10601 = .success := by decide +kernel
theorem unsat10601 : Unsatisfiable (PosFin 65) f10601 := by
  apply lratCheckerSound f10601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10601
  · intro a ha; simp [p10601] at ha; subst a; trivial
  · exact checked10601
theorem derived10601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10601 := by
  apply localUnsat_implies_entails f10601 [c9748, c2322] c10601 unsat10601 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2322 := h 2321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10602 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨16, by decide⟩, true), (⟨54, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2334, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10602 : lratChecker f10602 p10602 = .success := by decide +kernel
theorem unsat10602 : Unsatisfiable (PosFin 65) f10602 := by
  apply lratCheckerSound f10602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10602
  · intro a ha; simp [p10602] at ha; subst a; trivial
  · exact checked10602
theorem derived10602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10602 := by
  apply localUnsat_implies_entails f10602 [c9748, c2334] c10602 unsat10602 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2334 := h 2333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10603 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1592, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10603 : lratChecker f10603 p10603 = .success := by decide +kernel
theorem unsat10603 : Unsatisfiable (PosFin 65) f10603 := by
  apply lratCheckerSound f10603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10603
  · intro a ha; simp [p10603] at ha; subst a; trivial
  · exact checked10603
theorem derived10603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10603 := by
  apply localUnsat_implies_entails f10603 [c9748, c1592] c10603 unsat10603 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1592 := h 1591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10604 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2275, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10604 : lratChecker f10604 p10604 = .success := by decide +kernel
theorem unsat10604 : Unsatisfiable (PosFin 65) f10604 := by
  apply lratCheckerSound f10604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10604
  · intro a ha; simp [p10604] at ha; subst a; trivial
  · exact checked10604
theorem derived10604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10604 := by
  apply localUnsat_implies_entails f10604 [c9748, c2275] c10604 unsat10604 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2275 := h 2274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10605 : DefaultClause 65 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1872, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p10605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10605 : lratChecker f10605 p10605 = .success := by decide +kernel
theorem unsat10605 : Unsatisfiable (PosFin 65) f10605 := by
  apply lratCheckerSound f10605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10605
  · intro a ha; simp [p10605] at ha; subst a; trivial
  · exact checked10605
theorem derived10605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10605 := by
  apply localUnsat_implies_entails f10605 [c9748, c1872] c10605 unsat10605 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1872 := h 1871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10606 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨59, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1835, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10606 : lratChecker f10606 p10606 = .success := by decide +kernel
theorem unsat10606 : Unsatisfiable (PosFin 65) f10606 := by
  apply lratCheckerSound f10606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10606
  · intro a ha; simp [p10606] at ha; subst a; trivial
  · exact checked10606
theorem derived10606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10606 := by
  apply localUnsat_implies_entails f10606 [c9748, c1835] c10606 unsat10606 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1835 := h 1834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10607 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1833, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10607 : lratChecker f10607 p10607 = .success := by decide +kernel
theorem unsat10607 : Unsatisfiable (PosFin 65) f10607 := by
  apply lratCheckerSound f10607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10607
  · intro a ha; simp [p10607] at ha; subst a; trivial
  · exact checked10607
theorem derived10607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10607 := by
  apply localUnsat_implies_entails f10607 [c9748, c1833] c10607 unsat10607 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1833 := h 1832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10608 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1824, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10608 : lratChecker f10608 p10608 = .success := by decide +kernel
theorem unsat10608 : Unsatisfiable (PosFin 65) f10608 := by
  apply lratCheckerSound f10608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10608
  · intro a ha; simp [p10608] at ha; subst a; trivial
  · exact checked10608
theorem derived10608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10608 := by
  apply localUnsat_implies_entails f10608 [c9748, c1824] c10608 unsat10608 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1824 := h 1823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10609 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨13, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2332, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10609 : lratChecker f10609 p10609 = .success := by decide +kernel
theorem unsat10609 : Unsatisfiable (PosFin 65) f10609 := by
  apply lratCheckerSound f10609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10609
  · intro a ha; simp [p10609] at ha; subst a; trivial
  · exact checked10609
theorem derived10609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10609 := by
  apply localUnsat_implies_entails f10609 [c9748, c2332] c10609 unsat10609 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2332 := h 2331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10610 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2284, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p10610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10610 : lratChecker f10610 p10610 = .success := by decide +kernel
theorem unsat10610 : Unsatisfiable (PosFin 65) f10610 := by
  apply lratCheckerSound f10610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10610
  · intro a ha; simp [p10610] at ha; subst a; trivial
  · exact checked10610
theorem derived10610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10610 := by
  apply localUnsat_implies_entails f10610 [c9748, c2284] c10610 unsat10610 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2284 := h 2283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10611 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1839, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10611 : lratChecker f10611 p10611 = .success := by decide +kernel
theorem unsat10611 : Unsatisfiable (PosFin 65) f10611 := by
  apply lratCheckerSound f10611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10611
  · intro a ha; simp [p10611] at ha; subst a; trivial
  · exact checked10611
theorem derived10611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10611 := by
  apply localUnsat_implies_entails f10611 [c9748, c1839] c10611 unsat10611 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1839 := h 1838 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10612 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2280, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p10612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10612 : lratChecker f10612 p10612 = .success := by decide +kernel
theorem unsat10612 : Unsatisfiable (PosFin 65) f10612 := by
  apply lratCheckerSound f10612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10612
  · intro a ha; simp [p10612] at ha; subst a; trivial
  · exact checked10612
theorem derived10612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10612 := by
  apply localUnsat_implies_entails f10612 [c9748, c2280] c10612 unsat10612 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2280 := h 2279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10613 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2278, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10613 : lratChecker f10613 p10613 = .success := by decide +kernel
theorem unsat10613 : Unsatisfiable (PosFin 65) f10613 := by
  apply lratCheckerSound f10613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10613
  · intro a ha; simp [p10613] at ha; subst a; trivial
  · exact checked10613
theorem derived10613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10613 := by
  apply localUnsat_implies_entails f10613 [c9748, c2278] c10613 unsat10613 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2278 := h 2277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10614 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1632, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p10614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10614 : lratChecker f10614 p10614 = .success := by decide +kernel
theorem unsat10614 : Unsatisfiable (PosFin 65) f10614 := by
  apply lratCheckerSound f10614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10614
  · intro a ha; simp [p10614] at ha; subst a; trivial
  · exact checked10614
theorem derived10614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10614 := by
  apply localUnsat_implies_entails f10614 [c9748, c1632] c10614 unsat10614 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1632 := h 1631 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10615 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2282, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10615 : lratChecker f10615 p10615 = .success := by decide +kernel
theorem unsat10615 : Unsatisfiable (PosFin 65) f10615 := by
  apply lratCheckerSound f10615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10615
  · intro a ha; simp [p10615] at ha; subst a; trivial
  · exact checked10615
theorem derived10615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10615 := by
  apply localUnsat_implies_entails f10615 [c9748, c2282] c10615 unsat10615 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2282 := h 2281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10616 : DefaultClause 65 := directClause [(⟨38, by decide⟩, false), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1593, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10616 : lratChecker f10616 p10616 = .success := by decide +kernel
theorem unsat10616 : Unsatisfiable (PosFin 65) f10616 := by
  apply lratCheckerSound f10616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10616
  · intro a ha; simp [p10616] at ha; subst a; trivial
  · exact checked10616
theorem derived10616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10616 := by
  apply localUnsat_implies_entails f10616 [c9748, c1593] c10616 unsat10616 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1593 := h 1592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10617 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨31, by decide⟩, false), (⟨18, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2283, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10617 : lratChecker f10617 p10617 = .success := by decide +kernel
theorem unsat10617 : Unsatisfiable (PosFin 65) f10617 := by
  apply lratCheckerSound f10617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10617
  · intro a ha; simp [p10617] at ha; subst a; trivial
  · exact checked10617
theorem derived10617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10617 := by
  apply localUnsat_implies_entails f10617 [c9748, c2283] c10617 unsat10617 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2283 := h 2282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10618 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2310, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10618 : lratChecker f10618 p10618 = .success := by decide +kernel
theorem unsat10618 : Unsatisfiable (PosFin 65) f10618 := by
  apply lratCheckerSound f10618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10618
  · intro a ha; simp [p10618] at ha; subst a; trivial
  · exact checked10618
theorem derived10618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10618 := by
  apply localUnsat_implies_entails f10618 [c9748, c2310] c10618 unsat10618 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2310 := h 2309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10619 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2307, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10619 : lratChecker f10619 p10619 = .success := by decide +kernel
theorem unsat10619 : Unsatisfiable (PosFin 65) f10619 := by
  apply lratCheckerSound f10619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10619
  · intro a ha; simp [p10619] at ha; subst a; trivial
  · exact checked10619
theorem derived10619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10619 := by
  apply localUnsat_implies_entails f10619 [c9748, c2307] c10619 unsat10619 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2307 := h 2306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10620 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨16, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2323, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10620 : lratChecker f10620 p10620 = .success := by decide +kernel
theorem unsat10620 : Unsatisfiable (PosFin 65) f10620 := by
  apply lratCheckerSound f10620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10620
  · intro a ha; simp [p10620] at ha; subst a; trivial
  · exact checked10620
theorem derived10620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10620 := by
  apply localUnsat_implies_entails f10620 [c9748, c2323] c10620 unsat10620 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2323 := h 2322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10621 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1852, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10621 : lratChecker f10621 p10621 = .success := by decide +kernel
theorem unsat10621 : Unsatisfiable (PosFin 65) f10621 := by
  apply lratCheckerSound f10621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10621
  · intro a ha; simp [p10621] at ha; subst a; trivial
  · exact checked10621
theorem derived10621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10621 := by
  apply localUnsat_implies_entails f10621 [c9748, c1852] c10621 unsat10621 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1852 := h 1851 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10622 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1613, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10622 : lratChecker f10622 p10622 = .success := by decide +kernel
theorem unsat10622 : Unsatisfiable (PosFin 65) f10622 := by
  apply lratCheckerSound f10622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10622
  · intro a ha; simp [p10622] at ha; subst a; trivial
  · exact checked10622
theorem derived10622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10622 := by
  apply localUnsat_implies_entails f10622 [c9748, c1613] c10622 unsat10622 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1613 := h 1612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10623 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1844, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10623 : lratChecker f10623 p10623 = .success := by decide +kernel
theorem unsat10623 : Unsatisfiable (PosFin 65) f10623 := by
  apply lratCheckerSound f10623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10623
  · intro a ha; simp [p10623] at ha; subst a; trivial
  · exact checked10623
theorem derived10623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10623 := by
  apply localUnsat_implies_entails f10623 [c9748, c1844] c10623 unsat10623 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1844 := h 1843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10624 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2286, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10624 : lratChecker f10624 p10624 = .success := by decide +kernel
theorem unsat10624 : Unsatisfiable (PosFin 65) f10624 := by
  apply lratCheckerSound f10624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10624
  · intro a ha; simp [p10624] at ha; subst a; trivial
  · exact checked10624
theorem derived10624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10624 := by
  apply localUnsat_implies_entails f10624 [c9748, c2286] c10624 unsat10624 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2286 := h 2285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10625 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1857, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p10625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10625 : lratChecker f10625 p10625 = .success := by decide +kernel
theorem unsat10625 : Unsatisfiable (PosFin 65) f10625 := by
  apply lratCheckerSound f10625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10625
  · intro a ha; simp [p10625] at ha; subst a; trivial
  · exact checked10625
theorem derived10625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10625 := by
  apply localUnsat_implies_entails f10625 [c9748, c1857] c10625 unsat10625 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1857 := h 1856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10626 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2305, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10626 : lratChecker f10626 p10626 = .success := by decide +kernel
theorem unsat10626 : Unsatisfiable (PosFin 65) f10626 := by
  apply lratCheckerSound f10626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10626
  · intro a ha; simp [p10626] at ha; subst a; trivial
  · exact checked10626
theorem derived10626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10626 := by
  apply localUnsat_implies_entails f10626 [c9748, c2305] c10626 unsat10626 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2305 := h 2304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10627 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1601, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p10627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10627 : lratChecker f10627 p10627 = .success := by decide +kernel
theorem unsat10627 : Unsatisfiable (PosFin 65) f10627 := by
  apply lratCheckerSound f10627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10627
  · intro a ha; simp [p10627] at ha; subst a; trivial
  · exact checked10627
theorem derived10627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10627 := by
  apply localUnsat_implies_entails f10627 [c9748, c1601] c10627 unsat10627 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1601 := h 1600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10628 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1834, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p10628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10628 : lratChecker f10628 p10628 = .success := by decide +kernel
theorem unsat10628 : Unsatisfiable (PosFin 65) f10628 := by
  apply lratCheckerSound f10628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10628
  · intro a ha; simp [p10628] at ha; subst a; trivial
  · exact checked10628
theorem derived10628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10628 := by
  apply localUnsat_implies_entails f10628 [c9748, c1834] c10628 unsat10628 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1834 := h 1833 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10629 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1856, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p10629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10629 : lratChecker f10629 p10629 = .success := by decide +kernel
theorem unsat10629 : Unsatisfiable (PosFin 65) f10629 := by
  apply lratCheckerSound f10629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10629
  · intro a ha; simp [p10629] at ha; subst a; trivial
  · exact checked10629
theorem derived10629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10629 := by
  apply localUnsat_implies_entails f10629 [c9748, c1856] c10629 unsat10629 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1856 := h 1855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10630 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨26, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2298, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10630 : lratChecker f10630 p10630 = .success := by decide +kernel
theorem unsat10630 : Unsatisfiable (PosFin 65) f10630 := by
  apply lratCheckerSound f10630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10630
  · intro a ha; simp [p10630] at ha; subst a; trivial
  · exact checked10630
theorem derived10630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10630 := by
  apply localUnsat_implies_entails f10630 [c9748, c2298] c10630 unsat10630 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2298 := h 2297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10631 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1629, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10631 : lratChecker f10631 p10631 = .success := by decide +kernel
theorem unsat10631 : Unsatisfiable (PosFin 65) f10631 := by
  apply lratCheckerSound f10631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10631
  · intro a ha; simp [p10631] at ha; subst a; trivial
  · exact checked10631
theorem derived10631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10631 := by
  apply localUnsat_implies_entails f10631 [c9748, c1629] c10631 unsat10631 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1629 := h 1628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10632 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1631, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10632 : lratChecker f10632 p10632 = .success := by decide +kernel
theorem unsat10632 : Unsatisfiable (PosFin 65) f10632 := by
  apply lratCheckerSound f10632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10632
  · intro a ha; simp [p10632] at ha; subst a; trivial
  · exact checked10632
theorem derived10632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10632 := by
  apply localUnsat_implies_entails f10632 [c9748, c1631] c10632 unsat10632 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1631 := h 1630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10633 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2306, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10633 : lratChecker f10633 p10633 = .success := by decide +kernel
theorem unsat10633 : Unsatisfiable (PosFin 65) f10633 := by
  apply lratCheckerSound f10633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10633
  · intro a ha; simp [p10633] at ha; subst a; trivial
  · exact checked10633
theorem derived10633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10633 := by
  apply localUnsat_implies_entails f10633 [c9748, c2306] c10633 unsat10633 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2306 := h 2305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10634 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2336, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10634 : lratChecker f10634 p10634 = .success := by decide +kernel
theorem unsat10634 : Unsatisfiable (PosFin 65) f10634 := by
  apply lratCheckerSound f10634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10634
  · intro a ha; simp [p10634] at ha; subst a; trivial
  · exact checked10634
theorem derived10634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10634 := by
  apply localUnsat_implies_entails f10634 [c9748, c2336] c10634 unsat10634 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2336 := h 2335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10635 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨63, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2245, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10635 : lratChecker f10635 p10635 = .success := by decide +kernel
theorem unsat10635 : Unsatisfiable (PosFin 65) f10635 := by
  apply lratCheckerSound f10635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10635
  · intro a ha; simp [p10635] at ha; subst a; trivial
  · exact checked10635
theorem derived10635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10635 := by
  apply localUnsat_implies_entails f10635 [c9748, c2245] c10635 unsat10635 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2245 := h 2244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10636 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1792, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10636 : lratChecker f10636 p10636 = .success := by decide +kernel
theorem unsat10636 : Unsatisfiable (PosFin 65) f10636 := by
  apply lratCheckerSound f10636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10636
  · intro a ha; simp [p10636] at ha; subst a; trivial
  · exact checked10636
theorem derived10636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10636 := by
  apply localUnsat_implies_entails f10636 [c9748, c1792] c10636 unsat10636 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1792 := h 1791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10637 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨35, by decide⟩, false), (⟨59, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2233, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10637 : lratChecker f10637 p10637 = .success := by decide +kernel
theorem unsat10637 : Unsatisfiable (PosFin 65) f10637 := by
  apply lratCheckerSound f10637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10637
  · intro a ha; simp [p10637] at ha; subst a; trivial
  · exact checked10637
theorem derived10637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10637 := by
  apply localUnsat_implies_entails f10637 [c9748, c2233] c10637 unsat10637 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2233 := h 2232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10638 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1670, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10638 : lratChecker f10638 p10638 = .success := by decide +kernel
theorem unsat10638 : Unsatisfiable (PosFin 65) f10638 := by
  apply lratCheckerSound f10638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10638
  · intro a ha; simp [p10638] at ha; subst a; trivial
  · exact checked10638
theorem derived10638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10638 := by
  apply localUnsat_implies_entails f10638 [c9748, c1670] c10638 unsat10638 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1670 := h 1669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10639 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1676, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10639 : lratChecker f10639 p10639 = .success := by decide +kernel
theorem unsat10639 : Unsatisfiable (PosFin 65) f10639 := by
  apply lratCheckerSound f10639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10639
  · intro a ha; simp [p10639] at ha; subst a; trivial
  · exact checked10639
theorem derived10639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10639 := by
  apply localUnsat_implies_entails f10639 [c9748, c1676] c10639 unsat10639 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1676 := h 1675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10640 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2274, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10640 : lratChecker f10640 p10640 = .success := by decide +kernel
theorem unsat10640 : Unsatisfiable (PosFin 65) f10640 := by
  apply lratCheckerSound f10640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10640
  · intro a ha; simp [p10640] at ha; subst a; trivial
  · exact checked10640
theorem derived10640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10640 := by
  apply localUnsat_implies_entails f10640 [c9748, c2274] c10640 unsat10640 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2274 := h 2273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10641 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2185, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10641 : lratChecker f10641 p10641 = .success := by decide +kernel
theorem unsat10641 : Unsatisfiable (PosFin 65) f10641 := by
  apply lratCheckerSound f10641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10641
  · intro a ha; simp [p10641] at ha; subst a; trivial
  · exact checked10641
theorem derived10641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10641 := by
  apply localUnsat_implies_entails f10641 [c9748, c2185] c10641 unsat10641 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2185 := h 2184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10642 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2357, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10642 : lratChecker f10642 p10642 = .success := by decide +kernel
theorem unsat10642 : Unsatisfiable (PosFin 65) f10642 := by
  apply lratCheckerSound f10642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10642
  · intro a ha; simp [p10642] at ha; subst a; trivial
  · exact checked10642
theorem derived10642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10642 := by
  apply localUnsat_implies_entails f10642 [c9748, c2357] c10642 unsat10642 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2357 := h 2356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10643 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1677, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10643 : lratChecker f10643 p10643 = .success := by decide +kernel
theorem unsat10643 : Unsatisfiable (PosFin 65) f10643 := by
  apply lratCheckerSound f10643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10643
  · intro a ha; simp [p10643] at ha; subst a; trivial
  · exact checked10643
theorem derived10643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10643 := by
  apply localUnsat_implies_entails f10643 [c9748, c1677] c10643 unsat10643 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1677 := h 1676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10644 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1454, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10644 : lratChecker f10644 p10644 = .success := by decide +kernel
theorem unsat10644 : Unsatisfiable (PosFin 65) f10644 := by
  apply lratCheckerSound f10644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10644
  · intro a ha; simp [p10644] at ha; subst a; trivial
  · exact checked10644
theorem derived10644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10644 := by
  apply localUnsat_implies_entails f10644 [c9748, c1454] c10644 unsat10644 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1454 := h 1453 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10645 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1791, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10645 : lratChecker f10645 p10645 = .success := by decide +kernel
theorem unsat10645 : Unsatisfiable (PosFin 65) f10645 := by
  apply lratCheckerSound f10645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10645
  · intro a ha; simp [p10645] at ha; subst a; trivial
  · exact checked10645
theorem derived10645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10645 := by
  apply localUnsat_implies_entails f10645 [c9748, c1791] c10645 unsat10645 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1791 := h 1790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10646 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨58, by decide⟩, false), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2378, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10646 : lratChecker f10646 p10646 = .success := by decide +kernel
theorem unsat10646 : Unsatisfiable (PosFin 65) f10646 := by
  apply lratCheckerSound f10646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10646
  · intro a ha; simp [p10646] at ha; subst a; trivial
  · exact checked10646
theorem derived10646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10646 := by
  apply localUnsat_implies_entails f10646 [c9748, c2378] c10646 unsat10646 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2378 := h 2377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10647 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, false), (⟨6, by decide⟩, true), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1754, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10647 : lratChecker f10647 p10647 = .success := by decide +kernel
theorem unsat10647 : Unsatisfiable (PosFin 65) f10647 := by
  apply lratCheckerSound f10647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10647
  · intro a ha; simp [p10647] at ha; subst a; trivial
  · exact checked10647
theorem derived10647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10647 := by
  apply localUnsat_implies_entails f10647 [c9748, c1754] c10647 unsat10647 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1754 := h 1753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10648 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨60, by decide⟩, false), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1820, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10648 : lratChecker f10648 p10648 = .success := by decide +kernel
theorem unsat10648 : Unsatisfiable (PosFin 65) f10648 := by
  apply lratCheckerSound f10648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10648
  · intro a ha; simp [p10648] at ha; subst a; trivial
  · exact checked10648
theorem derived10648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10648 := by
  apply localUnsat_implies_entails f10648 [c9748, c1820] c10648 unsat10648 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1820 := h 1819 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10649 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1741, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10649 : lratChecker f10649 p10649 = .success := by decide +kernel
theorem unsat10649 : Unsatisfiable (PosFin 65) f10649 := by
  apply lratCheckerSound f10649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10649
  · intro a ha; simp [p10649] at ha; subst a; trivial
  · exact checked10649
theorem derived10649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10649 := by
  apply localUnsat_implies_entails f10649 [c9748, c1741] c10649 unsat10649 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1741 := h 1740 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10650 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨58, by decide⟩, false), (⟨61, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1961, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10650 : lratChecker f10650 p10650 = .success := by decide +kernel
theorem unsat10650 : Unsatisfiable (PosFin 65) f10650 := by
  apply lratCheckerSound f10650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10650
  · intro a ha; simp [p10650] at ha; subst a; trivial
  · exact checked10650
theorem derived10650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10650 := by
  apply localUnsat_implies_entails f10650 [c9748, c1961] c10650 unsat10650 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1961 := h 1960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10650

end CochromaticTwenty.Certificates.FixedCore0
