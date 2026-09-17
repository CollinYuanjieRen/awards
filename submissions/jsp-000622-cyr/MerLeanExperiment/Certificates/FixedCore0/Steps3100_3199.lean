import MerLeanExperiment.Certificates.FixedCore0.Steps3000_3099

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10651 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨58, by decide⟩, false), (⟨14, by decide⟩, true), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2373, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10651 : lratChecker f10651 p10651 = .success := by decide +kernel
theorem unsat10651 : Unsatisfiable (PosFin 65) f10651 := by
  apply lratCheckerSound f10651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10651
  · intro a ha; simp [p10651] at ha; subst a; trivial
  · exact checked10651
theorem derived10651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10651 := by
  apply localUnsat_implies_entails f10651 [c9748, c2373] c10651 unsat10651 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2373 := h 2372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10652 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨14, by decide⟩, true), (⟨54, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2261, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10652 : lratChecker f10652 p10652 = .success := by decide +kernel
theorem unsat10652 : Unsatisfiable (PosFin 65) f10652 := by
  apply lratCheckerSound f10652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10652
  · intro a ha; simp [p10652] at ha; subst a; trivial
  · exact checked10652
theorem derived10652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10652 := by
  apply localUnsat_implies_entails f10652 [c9748, c2261] c10652 unsat10652 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2261 := h 2260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10653 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1946, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10653 : lratChecker f10653 p10653 = .success := by decide +kernel
theorem unsat10653 : Unsatisfiable (PosFin 65) f10653 := by
  apply lratCheckerSound f10653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10653
  · intro a ha; simp [p10653] at ha; subst a; trivial
  · exact checked10653
theorem derived10653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10653 := by
  apply localUnsat_implies_entails f10653 [c9748, c1946] c10653 unsat10653 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1946 := h 1945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10654 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2263, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10654 : lratChecker f10654 p10654 = .success := by decide +kernel
theorem unsat10654 : Unsatisfiable (PosFin 65) f10654 := by
  apply lratCheckerSound f10654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10654
  · intro a ha; simp [p10654] at ha; subst a; trivial
  · exact checked10654
theorem derived10654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10654 := by
  apply localUnsat_implies_entails f10654 [c9748, c2263] c10654 unsat10654 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2263 := h 2262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10655 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2372, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10655 : lratChecker f10655 p10655 = .success := by decide +kernel
theorem unsat10655 : Unsatisfiable (PosFin 65) f10655 := by
  apply lratCheckerSound f10655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10655
  · intro a ha; simp [p10655] at ha; subst a; trivial
  · exact checked10655
theorem derived10655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10655 := by
  apply localUnsat_implies_entails f10655 [c9748, c2372] c10655 unsat10655 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2372 := h 2371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10656 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2026, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10656 : lratChecker f10656 p10656 = .success := by decide +kernel
theorem unsat10656 : Unsatisfiable (PosFin 65) f10656 := by
  apply lratCheckerSound f10656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10656
  · intro a ha; simp [p10656] at ha; subst a; trivial
  · exact checked10656
theorem derived10656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10656 := by
  apply localUnsat_implies_entails f10656 [c9748, c2026] c10656 unsat10656 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2026 := h 2025 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10657 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1515, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10657 : lratChecker f10657 p10657 = .success := by decide +kernel
theorem unsat10657 : Unsatisfiable (PosFin 65) f10657 := by
  apply lratCheckerSound f10657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10657
  · intro a ha; simp [p10657] at ha; subst a; trivial
  · exact checked10657
theorem derived10657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10657 := by
  apply localUnsat_implies_entails f10657 [c9748, c1515] c10657 unsat10657 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1515 := h 1514 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10658 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2217, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10658 : lratChecker f10658 p10658 = .success := by decide +kernel
theorem unsat10658 : Unsatisfiable (PosFin 65) f10658 := by
  apply lratCheckerSound f10658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10658
  · intro a ha; simp [p10658] at ha; subst a; trivial
  · exact checked10658
theorem derived10658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10658 := by
  apply localUnsat_implies_entails f10658 [c9748, c2217] c10658 unsat10658 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2217 := h 2216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10659 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1702, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10659 : lratChecker f10659 p10659 = .success := by decide +kernel
theorem unsat10659 : Unsatisfiable (PosFin 65) f10659 := by
  apply lratCheckerSound f10659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10659
  · intro a ha; simp [p10659] at ha; subst a; trivial
  · exact checked10659
theorem derived10659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10659 := by
  apply localUnsat_implies_entails f10659 [c9748, c1702] c10659 unsat10659 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1702 := h 1701 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10660 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2344, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10660 : lratChecker f10660 p10660 = .success := by decide +kernel
theorem unsat10660 : Unsatisfiable (PosFin 65) f10660 := by
  apply lratCheckerSound f10660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10660
  · intro a ha; simp [p10660] at ha; subst a; trivial
  · exact checked10660
theorem derived10660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10660 := by
  apply localUnsat_implies_entails f10660 [c9748, c2344] c10660 unsat10660 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2344 := h 2343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10661 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1917, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10661 : lratChecker f10661 p10661 = .success := by decide +kernel
theorem unsat10661 : Unsatisfiable (PosFin 65) f10661 := by
  apply lratCheckerSound f10661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10661
  · intro a ha; simp [p10661] at ha; subst a; trivial
  · exact checked10661
theorem derived10661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10661 := by
  apply localUnsat_implies_entails f10661 [c9748, c1917] c10661 unsat10661 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1917 := h 1916 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10662 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1985, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p10662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10662 : lratChecker f10662 p10662 = .success := by decide +kernel
theorem unsat10662 : Unsatisfiable (PosFin 65) f10662 := by
  apply lratCheckerSound f10662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10662
  · intro a ha; simp [p10662] at ha; subst a; trivial
  · exact checked10662
theorem derived10662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10662 := by
  apply localUnsat_implies_entails f10662 [c9748, c1985] c10662 unsat10662 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1985 := h 1984 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10663 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨32, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1987, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10663 : lratChecker f10663 p10663 = .success := by decide +kernel
theorem unsat10663 : Unsatisfiable (PosFin 65) f10663 := by
  apply lratCheckerSound f10663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10663
  · intro a ha; simp [p10663] at ha; subst a; trivial
  · exact checked10663
theorem derived10663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10663 := by
  apply localUnsat_implies_entails f10663 [c9748, c1987] c10663 unsat10663 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1987 := h 1986 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10664 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2212, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p10664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10664 : lratChecker f10664 p10664 = .success := by decide +kernel
theorem unsat10664 : Unsatisfiable (PosFin 65) f10664 := by
  apply lratCheckerSound f10664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10664
  · intro a ha; simp [p10664] at ha; subst a; trivial
  · exact checked10664
theorem derived10664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10664 := by
  apply localUnsat_implies_entails f10664 [c9748, c2212] c10664 unsat10664 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2212 := h 2211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10665 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨32, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2230, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10665 : lratChecker f10665 p10665 = .success := by decide +kernel
theorem unsat10665 : Unsatisfiable (PosFin 65) f10665 := by
  apply lratCheckerSound f10665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10665
  · intro a ha; simp [p10665] at ha; subst a; trivial
  · exact checked10665
theorem derived10665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10665 := by
  apply localUnsat_implies_entails f10665 [c9748, c2230] c10665 unsat10665 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2230 := h 2229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10666 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1716, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p10666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10666 : lratChecker f10666 p10666 = .success := by decide +kernel
theorem unsat10666 : Unsatisfiable (PosFin 65) f10666 := by
  apply lratCheckerSound f10666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10666
  · intro a ha; simp [p10666] at ha; subst a; trivial
  · exact checked10666
theorem derived10666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10666 := by
  apply localUnsat_implies_entails f10666 [c9748, c1716] c10666 unsat10666 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1716 := h 1715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10667 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1765, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10667 : lratChecker f10667 p10667 = .success := by decide +kernel
theorem unsat10667 : Unsatisfiable (PosFin 65) f10667 := by
  apply lratCheckerSound f10667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10667
  · intro a ha; simp [p10667] at ha; subst a; trivial
  · exact checked10667
theorem derived10667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10667 := by
  apply localUnsat_implies_entails f10667 [c9748, c1765] c10667 unsat10667 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1765 := h 1764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10668 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2199, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10668 : lratChecker f10668 p10668 = .success := by decide +kernel
theorem unsat10668 : Unsatisfiable (PosFin 65) f10668 := by
  apply lratCheckerSound f10668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10668
  · intro a ha; simp [p10668] at ha; subst a; trivial
  · exact checked10668
theorem derived10668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10668 := by
  apply localUnsat_implies_entails f10668 [c9748, c2199] c10668 unsat10668 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2199 := h 2198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10669 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1768, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10669 : lratChecker f10669 p10669 = .success := by decide +kernel
theorem unsat10669 : Unsatisfiable (PosFin 65) f10669 := by
  apply lratCheckerSound f10669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10669
  · intro a ha; simp [p10669] at ha; subst a; trivial
  · exact checked10669
theorem derived10669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10669 := by
  apply localUnsat_implies_entails f10669 [c9748, c1768] c10669 unsat10669 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1768 := h 1767 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10670 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1996, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p10670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10670 : lratChecker f10670 p10670 = .success := by decide +kernel
theorem unsat10670 : Unsatisfiable (PosFin 65) f10670 := by
  apply lratCheckerSound f10670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10670
  · intro a ha; simp [p10670] at ha; subst a; trivial
  · exact checked10670
theorem derived10670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10670 := by
  apply localUnsat_implies_entails f10670 [c9748, c1996] c10670 unsat10670 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1996 := h 1995 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10671 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1766, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p10671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10671 : lratChecker f10671 p10671 = .success := by decide +kernel
theorem unsat10671 : Unsatisfiable (PosFin 65) f10671 := by
  apply lratCheckerSound f10671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10671
  · intro a ha; simp [p10671] at ha; subst a; trivial
  · exact checked10671
theorem derived10671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10671 := by
  apply localUnsat_implies_entails f10671 [c9748, c1766] c10671 unsat10671 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1766 := h 1765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10672 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1688, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p10672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10672 : lratChecker f10672 p10672 = .success := by decide +kernel
theorem unsat10672 : Unsatisfiable (PosFin 65) f10672 := by
  apply lratCheckerSound f10672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10672
  · intro a ha; simp [p10672] at ha; subst a; trivial
  · exact checked10672
theorem derived10672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10672 := by
  apply localUnsat_implies_entails f10672 [c9748, c1688] c10672 unsat10672 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1688 := h 1687 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10673 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1476, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p10673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10673 : lratChecker f10673 p10673 = .success := by decide +kernel
theorem unsat10673 : Unsatisfiable (PosFin 65) f10673 := by
  apply lratCheckerSound f10673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10673
  · intro a ha; simp [p10673] at ha; subst a; trivial
  · exact checked10673
theorem derived10673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10673 := by
  apply localUnsat_implies_entails f10673 [c9748, c1476] c10673 unsat10673 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1476 := h 1475 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10674 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1709, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10674 : lratChecker f10674 p10674 = .success := by decide +kernel
theorem unsat10674 : Unsatisfiable (PosFin 65) f10674 := by
  apply lratCheckerSound f10674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10674
  · intro a ha; simp [p10674] at ha; subst a; trivial
  · exact checked10674
theorem derived10674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10674 := by
  apply localUnsat_implies_entails f10674 [c9748, c1709] c10674 unsat10674 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1709 := h 1708 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10675 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1931, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10675 : lratChecker f10675 p10675 = .success := by decide +kernel
theorem unsat10675 : Unsatisfiable (PosFin 65) f10675 := by
  apply lratCheckerSound f10675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10675
  · intro a ha; simp [p10675] at ha; subst a; trivial
  · exact checked10675
theorem derived10675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10675 := by
  apply localUnsat_implies_entails f10675 [c9748, c1931] c10675 unsat10675 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1931 := h 1930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10676 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2051, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10676 : lratChecker f10676 p10676 = .success := by decide +kernel
theorem unsat10676 : Unsatisfiable (PosFin 65) f10676 := by
  apply lratCheckerSound f10676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10676
  · intro a ha; simp [p10676] at ha; subst a; trivial
  · exact checked10676
theorem derived10676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10676 := by
  apply localUnsat_implies_entails f10676 [c9748, c2051] c10676 unsat10676 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2051 := h 2050 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10677 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2346, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p10677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10677 : lratChecker f10677 p10677 = .success := by decide +kernel
theorem unsat10677 : Unsatisfiable (PosFin 65) f10677 := by
  apply lratCheckerSound f10677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10677
  · intro a ha; simp [p10677] at ha; subst a; trivial
  · exact checked10677
theorem derived10677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10677 := by
  apply localUnsat_implies_entails f10677 [c9748, c2346] c10677 unsat10677 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2346 := h 2345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10678 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1927, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10678 : lratChecker f10678 p10678 = .success := by decide +kernel
theorem unsat10678 : Unsatisfiable (PosFin 65) f10678 := by
  apply lratCheckerSound f10678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10678
  · intro a ha; simp [p10678] at ha; subst a; trivial
  · exact checked10678
theorem derived10678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10678 := by
  apply localUnsat_implies_entails f10678 [c9748, c1927] c10678 unsat10678 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1927 := h 1926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10679 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2042, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10679 : lratChecker f10679 p10679 = .success := by decide +kernel
theorem unsat10679 : Unsatisfiable (PosFin 65) f10679 := by
  apply lratCheckerSound f10679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10679
  · intro a ha; simp [p10679] at ha; subst a; trivial
  · exact checked10679
theorem derived10679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10679 := by
  apply localUnsat_implies_entails f10679 [c9748, c2042] c10679 unsat10679 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2042 := h 2041 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10680 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1995, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10680 : lratChecker f10680 p10680 = .success := by decide +kernel
theorem unsat10680 : Unsatisfiable (PosFin 65) f10680 := by
  apply lratCheckerSound f10680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10680
  · intro a ha; simp [p10680] at ha; subst a; trivial
  · exact checked10680
theorem derived10680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10680 := by
  apply localUnsat_implies_entails f10680 [c9748, c1995] c10680 unsat10680 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1995 := h 1994 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10681 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1712, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10681 : lratChecker f10681 p10681 = .success := by decide +kernel
theorem unsat10681 : Unsatisfiable (PosFin 65) f10681 := by
  apply lratCheckerSound f10681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10681
  · intro a ha; simp [p10681] at ha; subst a; trivial
  · exact checked10681
theorem derived10681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10681 := by
  apply localUnsat_implies_entails f10681 [c9748, c1712] c10681 unsat10681 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1712 := h 1711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10682 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1780, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p10682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10682 : lratChecker f10682 p10682 = .success := by decide +kernel
theorem unsat10682 : Unsatisfiable (PosFin 65) f10682 := by
  apply lratCheckerSound f10682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10682
  · intro a ha; simp [p10682] at ha; subst a; trivial
  · exact checked10682
theorem derived10682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10682 := by
  apply localUnsat_implies_entails f10682 [c9748, c1780] c10682 unsat10682 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1780 := h 1779 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10683 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2224, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10683 : lratChecker f10683 p10683 = .success := by decide +kernel
theorem unsat10683 : Unsatisfiable (PosFin 65) f10683 := by
  apply lratCheckerSound f10683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10683
  · intro a ha; simp [p10683] at ha; subst a; trivial
  · exact checked10683
theorem derived10683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10683 := by
  apply localUnsat_implies_entails f10683 [c9748, c2224] c10683 unsat10683 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2224 := h 2223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10684 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1781, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10684 : lratChecker f10684 p10684 = .success := by decide +kernel
theorem unsat10684 : Unsatisfiable (PosFin 65) f10684 := by
  apply lratCheckerSound f10684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10684
  · intro a ha; simp [p10684] at ha; subst a; trivial
  · exact checked10684
theorem derived10684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10684 := by
  apply localUnsat_implies_entails f10684 [c9748, c1781] c10684 unsat10684 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1781 := h 1780 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10685 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2228, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10685 : lratChecker f10685 p10685 = .success := by decide +kernel
theorem unsat10685 : Unsatisfiable (PosFin 65) f10685 := by
  apply lratCheckerSound f10685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10685
  · intro a ha; simp [p10685] at ha; subst a; trivial
  · exact checked10685
theorem derived10685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10685 := by
  apply localUnsat_implies_entails f10685 [c9748, c2228] c10685 unsat10685 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2228 := h 2227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10686 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨59, by decide⟩, false), (⟨19, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1598, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10686 : lratChecker f10686 p10686 = .success := by decide +kernel
theorem unsat10686 : Unsatisfiable (PosFin 65) f10686 := by
  apply lratCheckerSound f10686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10686
  · intro a ha; simp [p10686] at ha; subst a; trivial
  · exact checked10686
theorem derived10686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10686 := by
  apply localUnsat_implies_entails f10686 [c9748, c1598] c10686 unsat10686 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1598 := h 1597 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10687 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1621, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10687 : lratChecker f10687 p10687 = .success := by decide +kernel
theorem unsat10687 : Unsatisfiable (PosFin 65) f10687 := by
  apply lratCheckerSound f10687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10687
  · intro a ha; simp [p10687] at ha; subst a; trivial
  · exact checked10687
theorem derived10687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10687 := by
  apply localUnsat_implies_entails f10687 [c9748, c1621] c10687 unsat10687 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1621 := h 1620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10688 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1853, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p10688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10688 : lratChecker f10688 p10688 = .success := by decide +kernel
theorem unsat10688 : Unsatisfiable (PosFin 65) f10688 := by
  apply lratCheckerSound f10688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10688
  · intro a ha; simp [p10688] at ha; subst a; trivial
  · exact checked10688
theorem derived10688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10688 := by
  apply localUnsat_implies_entails f10688 [c9748, c1853] c10688 unsat10688 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1853 := h 1852 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10689 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨59, by decide⟩, false), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2184, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10689 : lratChecker f10689 p10689 = .success := by decide +kernel
theorem unsat10689 : Unsatisfiable (PosFin 65) f10689 := by
  apply lratCheckerSound f10689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10689
  · intro a ha; simp [p10689] at ha; subst a; trivial
  · exact checked10689
theorem derived10689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10689 := by
  apply localUnsat_implies_entails f10689 [c9748, c2184] c10689 unsat10689 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2184 := h 2183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10690 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2295, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10690 : lratChecker f10690 p10690 = .success := by decide +kernel
theorem unsat10690 : Unsatisfiable (PosFin 65) f10690 := by
  apply lratCheckerSound f10690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10690
  · intro a ha; simp [p10690] at ha; subst a; trivial
  · exact checked10690
theorem derived10690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10690 := by
  apply localUnsat_implies_entails f10690 [c9748, c2295] c10690 unsat10690 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2295 := h 2294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10691 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1777, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10691 : lratChecker f10691 p10691 = .success := by decide +kernel
theorem unsat10691 : Unsatisfiable (PosFin 65) f10691 := by
  apply lratCheckerSound f10691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10691
  · intro a ha; simp [p10691] at ha; subst a; trivial
  · exact checked10691
theorem derived10691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10691 := by
  apply localUnsat_implies_entails f10691 [c9748, c1777] c10691 unsat10691 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1777 := h 1776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10692 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1693, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10692 : lratChecker f10692 p10692 = .success := by decide +kernel
theorem unsat10692 : Unsatisfiable (PosFin 65) f10692 := by
  apply lratCheckerSound f10692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10692
  · intro a ha; simp [p10692] at ha; subst a; trivial
  · exact checked10692
theorem derived10692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10692 := by
  apply localUnsat_implies_entails f10692 [c9748, c1693] c10692 unsat10692 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1693 := h 1692 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10693 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1977, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10693 : lratChecker f10693 p10693 = .success := by decide +kernel
theorem unsat10693 : Unsatisfiable (PosFin 65) f10693 := by
  apply lratCheckerSound f10693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10693
  · intro a ha; simp [p10693] at ha; subst a; trivial
  · exact checked10693
theorem derived10693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10693 := by
  apply localUnsat_implies_entails f10693 [c9748, c1977] c10693 unsat10693 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1977 := h 1976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10694 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1769, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10694 : lratChecker f10694 p10694 = .success := by decide +kernel
theorem unsat10694 : Unsatisfiable (PosFin 65) f10694 := by
  apply lratCheckerSound f10694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10694
  · intro a ha; simp [p10694] at ha; subst a; trivial
  · exact checked10694
theorem derived10694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10694 := by
  apply localUnsat_implies_entails f10694 [c9748, c1769] c10694 unsat10694 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1769 := h 1768 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10695 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2204, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10695 : lratChecker f10695 p10695 = .success := by decide +kernel
theorem unsat10695 : Unsatisfiable (PosFin 65) f10695 := by
  apply lratCheckerSound f10695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10695
  · intro a ha; simp [p10695] at ha; subst a; trivial
  · exact checked10695
theorem derived10695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10695 := by
  apply localUnsat_implies_entails f10695 [c9748, c2204] c10695 unsat10695 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2204 := h 2203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10696 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2041, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10696 : lratChecker f10696 p10696 = .success := by decide +kernel
theorem unsat10696 : Unsatisfiable (PosFin 65) f10696 := by
  apply lratCheckerSound f10696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10696
  · intro a ha; simp [p10696] at ha; subst a; trivial
  · exact checked10696
theorem derived10696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10696 := by
  apply localUnsat_implies_entails f10696 [c9748, c2041] c10696 unsat10696 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2041 := h 2040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10697 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2341, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10697 : lratChecker f10697 p10697 = .success := by decide +kernel
theorem unsat10697 : Unsatisfiable (PosFin 65) f10697 := by
  apply lratCheckerSound f10697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10697
  · intro a ha; simp [p10697] at ha; subst a; trivial
  · exact checked10697
theorem derived10697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10697 := by
  apply localUnsat_implies_entails f10697 [c9748, c2341] c10697 unsat10697 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2341 := h 2340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10698 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1846, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10698 : lratChecker f10698 p10698 = .success := by decide +kernel
theorem unsat10698 : Unsatisfiable (PosFin 65) f10698 := by
  apply lratCheckerSound f10698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10698
  · intro a ha; simp [p10698] at ha; subst a; trivial
  · exact checked10698
theorem derived10698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10698 := by
  apply localUnsat_implies_entails f10698 [c9748, c1846] c10698 unsat10698 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1846 := h 1845 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10699 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2290, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10699 : lratChecker f10699 p10699 = .success := by decide +kernel
theorem unsat10699 : Unsatisfiable (PosFin 65) f10699 := by
  apply lratCheckerSound f10699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10699
  · intro a ha; simp [p10699] at ha; subst a; trivial
  · exact checked10699
theorem derived10699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10699 := by
  apply localUnsat_implies_entails f10699 [c9748, c2290] c10699 unsat10699 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2290 := h 2289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10700 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2049, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10700 : lratChecker f10700 p10700 = .success := by decide +kernel
theorem unsat10700 : Unsatisfiable (PosFin 65) f10700 := by
  apply lratCheckerSound f10700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10700
  · intro a ha; simp [p10700] at ha; subst a; trivial
  · exact checked10700
theorem derived10700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10700 := by
  apply localUnsat_implies_entails f10700 [c9748, c2049] c10700 unsat10700 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2049 := h 2048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10701 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2347, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10701 : lratChecker f10701 p10701 = .success := by decide +kernel
theorem unsat10701 : Unsatisfiable (PosFin 65) f10701 := by
  apply lratCheckerSound f10701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10701
  · intro a ha; simp [p10701] at ha; subst a; trivial
  · exact checked10701
theorem derived10701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10701 := by
  apply localUnsat_implies_entails f10701 [c9748, c2347] c10701 unsat10701 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2347 := h 2346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10702 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1706, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10702 : lratChecker f10702 p10702 = .success := by decide +kernel
theorem unsat10702 : Unsatisfiable (PosFin 65) f10702 := by
  apply lratCheckerSound f10702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10702
  · intro a ha; simp [p10702] at ha; subst a; trivial
  · exact checked10702
theorem derived10702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10702 := by
  apply localUnsat_implies_entails f10702 [c9748, c1706] c10702 unsat10702 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1706 := h 1705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10703 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1988, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10703 : lratChecker f10703 p10703 = .success := by decide +kernel
theorem unsat10703 : Unsatisfiable (PosFin 65) f10703 := by
  apply lratCheckerSound f10703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10703
  · intro a ha; simp [p10703] at ha; subst a; trivial
  · exact checked10703
theorem derived10703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10703 := by
  apply localUnsat_implies_entails f10703 [c9748, c1988] c10703 unsat10703 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1988 := h 1987 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10704 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1776, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10704 : lratChecker f10704 p10704 = .success := by decide +kernel
theorem unsat10704 : Unsatisfiable (PosFin 65) f10704 := by
  apply lratCheckerSound f10704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10704
  · intro a ha; simp [p10704] at ha; subst a; trivial
  · exact checked10704
theorem derived10704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10704 := by
  apply localUnsat_implies_entails f10704 [c9748, c1776] c10704 unsat10704 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1776 := h 1775 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10705 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2216, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10705 : lratChecker f10705 p10705 = .success := by decide +kernel
theorem unsat10705 : Unsatisfiable (PosFin 65) f10705 := by
  apply lratCheckerSound f10705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10705
  · intro a ha; simp [p10705] at ha; subst a; trivial
  · exact checked10705
theorem derived10705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10705 := by
  apply localUnsat_implies_entails f10705 [c9748, c2216] c10705 unsat10705 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2216 := h 2215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10706 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1863, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10706 : lratChecker f10706 p10706 = .success := by decide +kernel
theorem unsat10706 : Unsatisfiable (PosFin 65) f10706 := by
  apply lratCheckerSound f10706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10706
  · intro a ha; simp [p10706] at ha; subst a; trivial
  · exact checked10706
theorem derived10706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10706 := by
  apply localUnsat_implies_entails f10706 [c9748, c1863] c10706 unsat10706 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1863 := h 1862 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10707 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2301, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p10707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10707 : lratChecker f10707 p10707 = .success := by decide +kernel
theorem unsat10707 : Unsatisfiable (PosFin 65) f10707 := by
  apply lratCheckerSound f10707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10707
  · intro a ha; simp [p10707] at ha; subst a; trivial
  · exact checked10707
theorem derived10707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10707 := by
  apply localUnsat_implies_entails f10707 [c9748, c2301] c10707 unsat10707 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2301 := h 2300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10708 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨52, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1464, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10708 : lratChecker f10708 p10708 = .success := by decide +kernel
theorem unsat10708 : Unsatisfiable (PosFin 65) f10708 := by
  apply lratCheckerSound f10708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10708
  · intro a ha; simp [p10708] at ha; subst a; trivial
  · exact checked10708
theorem derived10708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10708 := by
  apply localUnsat_implies_entails f10708 [c9748, c1464] c10708 unsat10708 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1464 := h 1463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10709 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2367, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10709 : lratChecker f10709 p10709 = .success := by decide +kernel
theorem unsat10709 : Unsatisfiable (PosFin 65) f10709 := by
  apply lratCheckerSound f10709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10709
  · intro a ha; simp [p10709] at ha; subst a; trivial
  · exact checked10709
theorem derived10709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10709 := by
  apply localUnsat_implies_entails f10709 [c9748, c2367] c10709 unsat10709 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2367 := h 2366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10710 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨59, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2062, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true))]
def p10710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10710 : lratChecker f10710 p10710 = .success := by decide +kernel
theorem unsat10710 : Unsatisfiable (PosFin 65) f10710 := by
  apply lratCheckerSound f10710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10710
  · intro a ha; simp [p10710] at ha; subst a; trivial
  · exact checked10710
theorem derived10710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10710 := by
  apply localUnsat_implies_entails f10710 [c9748, c2062] c10710 unsat10710 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2062 := h 2061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10711 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1757, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10711 : lratChecker f10711 p10711 = .success := by decide +kernel
theorem unsat10711 : Unsatisfiable (PosFin 65) f10711 := by
  apply lratCheckerSound f10711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10711
  · intro a ha; simp [p10711] at ha; subst a; trivial
  · exact checked10711
theorem derived10711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10711 := by
  apply localUnsat_implies_entails f10711 [c9748, c1757] c10711 unsat10711 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1757 := h 1756 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10712 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2182, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10712 : lratChecker f10712 p10712 = .success := by decide +kernel
theorem unsat10712 : Unsatisfiable (PosFin 65) f10712 := by
  apply lratCheckerSound f10712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10712
  · intro a ha; simp [p10712] at ha; subst a; trivial
  · exact checked10712
theorem derived10712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10712 := by
  apply localUnsat_implies_entails f10712 [c9748, c2182] c10712 unsat10712 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2182 := h 2181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10713 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2187, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p10713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10713 : lratChecker f10713 p10713 = .success := by decide +kernel
theorem unsat10713 : Unsatisfiable (PosFin 65) f10713 := by
  apply lratCheckerSound f10713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10713
  · intro a ha; simp [p10713] at ha; subst a; trivial
  · exact checked10713
theorem derived10713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10713 := by
  apply localUnsat_implies_entails f10713 [c9748, c2187] c10713 unsat10713 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2187 := h 2186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10714 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨57, by decide⟩, false), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2368, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10714 : lratChecker f10714 p10714 = .success := by decide +kernel
theorem unsat10714 : Unsatisfiable (PosFin 65) f10714 := by
  apply lratCheckerSound f10714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10714
  · intro a ha; simp [p10714] at ha; subst a; trivial
  · exact checked10714
theorem derived10714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10714 := by
  apply localUnsat_implies_entails f10714 [c9748, c2368] c10714 unsat10714 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2368 := h 2367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10715 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨57, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2020, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10715 : lratChecker f10715 p10715 = .success := by decide +kernel
theorem unsat10715 : Unsatisfiable (PosFin 65) f10715 := by
  apply lratCheckerSound f10715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10715
  · intro a ha; simp [p10715] at ha; subst a; trivial
  · exact checked10715
theorem derived10715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10715 := by
  apply localUnsat_implies_entails f10715 [c9748, c2020] c10715 unsat10715 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2020 := h 2019 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10716 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨59, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2031, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p10716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10716 : lratChecker f10716 p10716 = .success := by decide +kernel
theorem unsat10716 : Unsatisfiable (PosFin 65) f10716 := by
  apply lratCheckerSound f10716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10716
  · intro a ha; simp [p10716] at ha; subst a; trivial
  · exact checked10716
theorem derived10716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10716 := by
  apply localUnsat_implies_entails f10716 [c9748, c2031] c10716 unsat10716 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2031 := h 2030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10717 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1734, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10717 : lratChecker f10717 p10717 = .success := by decide +kernel
theorem unsat10717 : Unsatisfiable (PosFin 65) f10717 := by
  apply lratCheckerSound f10717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10717
  · intro a ha; simp [p10717] at ha; subst a; trivial
  · exact checked10717
theorem derived10717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10717 := by
  apply localUnsat_implies_entails f10717 [c9748, c1734] c10717 unsat10717 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1734 := h 1733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10718 : DefaultClause 65 := directClause [(⟨63, by decide⟩, false), (⟨50, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1500, some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10718 : lratChecker f10718 p10718 = .success := by decide +kernel
theorem unsat10718 : Unsatisfiable (PosFin 65) f10718 := by
  apply lratCheckerSound f10718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10718
  · intro a ha; simp [p10718] at ha; subst a; trivial
  · exact checked10718
theorem derived10718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10718 := by
  apply localUnsat_implies_entails f10718 [c9748, c1500] c10718 unsat10718 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1500 := h 1499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10719 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, true), (⟨53, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1959, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10719 : lratChecker f10719 p10719 = .success := by decide +kernel
theorem unsat10719 : Unsatisfiable (PosFin 65) f10719 := by
  apply lratCheckerSound f10719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10719
  · intro a ha; simp [p10719] at ha; subst a; trivial
  · exact checked10719
theorem derived10719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10719 := by
  apply localUnsat_implies_entails f10719 [c9748, c1959] c10719 unsat10719 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1959 := h 1958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10720 : DefaultClause 65 := directClause [(⟨62, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1963, some (DefaultClause.unit (⟨62, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10720 : lratChecker f10720 p10720 = .success := by decide +kernel
theorem unsat10720 : Unsatisfiable (PosFin 65) f10720 := by
  apply lratCheckerSound f10720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10720
  · intro a ha; simp [p10720] at ha; subst a; trivial
  · exact checked10720
theorem derived10720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10720 := by
  apply localUnsat_implies_entails f10720 [c9748, c1963] c10720 unsat10720 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1963 := h 1962 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10721 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1962, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10721 : lratChecker f10721 p10721 = .success := by decide +kernel
theorem unsat10721 : Unsatisfiable (PosFin 65) f10721 := by
  apply lratCheckerSound f10721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10721
  · intro a ha; simp [p10721] at ha; subst a; trivial
  · exact checked10721
theorem derived10721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10721 := by
  apply localUnsat_implies_entails f10721 [c9748, c1962] c10721 unsat10721 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1962 := h 1961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10722 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨58, by decide⟩, true), (⟨7, by decide⟩, true), (⟨63, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1530, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p10722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10722 : lratChecker f10722 p10722 = .success := by decide +kernel
theorem unsat10722 : Unsatisfiable (PosFin 65) f10722 := by
  apply lratCheckerSound f10722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10722
  · intro a ha; simp [p10722] at ha; subst a; trivial
  · exact checked10722
theorem derived10722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10722 := by
  apply localUnsat_implies_entails f10722 [c9748, c1530] c10722 unsat10722 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1530 := h 1529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10723 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨57, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1459, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true))]
def p10723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10723 : lratChecker f10723 p10723 = .success := by decide +kernel
theorem unsat10723 : Unsatisfiable (PosFin 65) f10723 := by
  apply lratCheckerSound f10723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10723
  · intro a ha; simp [p10723] at ha; subst a; trivial
  · exact checked10723
theorem derived10723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10723 := by
  apply localUnsat_implies_entails f10723 [c9748, c1459] c10723 unsat10723 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1459 := h 1458 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10724 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, false), (⟨8, by decide⟩, true), (⟨61, by decide⟩, false), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1755, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10724 : lratChecker f10724 p10724 = .success := by decide +kernel
theorem unsat10724 : Unsatisfiable (PosFin 65) f10724 := by
  apply lratCheckerSound f10724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10724
  · intro a ha; simp [p10724] at ha; subst a; trivial
  · exact checked10724
theorem derived10724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10724 := by
  apply localUnsat_implies_entails f10724 [c9748, c1755] c10724 unsat10724 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1755 := h 1754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10725 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨63, by decide⟩, false), (⟨54, by decide⟩, false), (⟨61, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1965, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10725 : lratChecker f10725 p10725 = .success := by decide +kernel
theorem unsat10725 : Unsatisfiable (PosFin 65) f10725 := by
  apply lratCheckerSound f10725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10725
  · intro a ha; simp [p10725] at ha; subst a; trivial
  · exact checked10725
theorem derived10725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10725 := by
  apply localUnsat_implies_entails f10725 [c9748, c1965] c10725 unsat10725 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1965 := h 1964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10726 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1669, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10726 : lratChecker f10726 p10726 = .success := by decide +kernel
theorem unsat10726 : Unsatisfiable (PosFin 65) f10726 := by
  apply lratCheckerSound f10726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10726
  · intro a ha; simp [p10726] at ha; subst a; trivial
  · exact checked10726
theorem derived10726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10726 := by
  apply localUnsat_implies_entails f10726 [c9748, c1669] c10726 unsat10726 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1669 := h 1668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10727 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, false), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨63, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1737, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true))]
def p10727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10727 : lratChecker f10727 p10727 = .success := by decide +kernel
theorem unsat10727 : Unsatisfiable (PosFin 65) f10727 := by
  apply lratCheckerSound f10727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10727
  · intro a ha; simp [p10727] at ha; subst a; trivial
  · exact checked10727
theorem derived10727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10727 := by
  apply localUnsat_implies_entails f10727 [c9748, c1737] c10727 unsat10727 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1737 := h 1736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10728 : DefaultClause 65 := directClause [(⟨37, by decide⟩, false), (⟨21, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1672, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10728 : lratChecker f10728 p10728 = .success := by decide +kernel
theorem unsat10728 : Unsatisfiable (PosFin 65) f10728 := by
  apply lratCheckerSound f10728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10728
  · intro a ha; simp [p10728] at ha; subst a; trivial
  · exact checked10728
theorem derived10728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10728 := by
  apply localUnsat_implies_entails f10728 [c9748, c1672] c10728 unsat10728 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1672 := h 1671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10729 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1954, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10729 : lratChecker f10729 p10729 = .success := by decide +kernel
theorem unsat10729 : Unsatisfiable (PosFin 65) f10729 := by
  apply lratCheckerSound f10729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10729
  · intro a ha; simp [p10729] at ha; subst a; trivial
  · exact checked10729
theorem derived10729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10729 := by
  apply localUnsat_implies_entails f10729 [c9748, c1954] c10729 unsat10729 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1954 := h 1953 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10730 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨59, by decide⟩, false), (⟨61, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1958, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10730 : lratChecker f10730 p10730 = .success := by decide +kernel
theorem unsat10730 : Unsatisfiable (PosFin 65) f10730 := by
  apply lratCheckerSound f10730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10730
  · intro a ha; simp [p10730] at ha; subst a; trivial
  · exact checked10730
theorem derived10730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10730 := by
  apply localUnsat_implies_entails f10730 [c9748, c1958] c10730 unsat10730 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1958 := h 1957 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10731 : DefaultClause 65 := directClause [(⟨36, by decide⟩, false), (⟨20, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1671, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p10731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10731 : lratChecker f10731 p10731 = .success := by decide +kernel
theorem unsat10731 : Unsatisfiable (PosFin 65) f10731 := by
  apply lratCheckerSound f10731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10731
  · intro a ha; simp [p10731] at ha; subst a; trivial
  · exact checked10731
theorem derived10731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10731 := by
  apply localUnsat_implies_entails f10731 [c9748, c1671] c10731 unsat10731 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1671 := h 1670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10732 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1932, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10732 : lratChecker f10732 p10732 = .success := by decide +kernel
theorem unsat10732 : Unsatisfiable (PosFin 65) f10732 := by
  apply lratCheckerSound f10732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10732
  · intro a ha; simp [p10732] at ha; subst a; trivial
  · exact checked10732
theorem derived10732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10732 := by
  apply localUnsat_implies_entails f10732 [c9748, c1932] c10732 unsat10732 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1932 := h 1931 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10733 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2038, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10733 : lratChecker f10733 p10733 = .success := by decide +kernel
theorem unsat10733 : Unsatisfiable (PosFin 65) f10733 := by
  apply lratCheckerSound f10733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10733
  · intro a ha; simp [p10733] at ha; subst a; trivial
  · exact checked10733
theorem derived10733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10733 := by
  apply localUnsat_implies_entails f10733 [c9748, c2038] c10733 unsat10733 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2038 := h 2037 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10734 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1714, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10734 : lratChecker f10734 p10734 = .success := by decide +kernel
theorem unsat10734 : Unsatisfiable (PosFin 65) f10734 := by
  apply lratCheckerSound f10734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10734
  · intro a ha; simp [p10734] at ha; subst a; trivial
  · exact checked10734
theorem derived10734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10734 := by
  apply localUnsat_implies_entails f10734 [c9748, c1714] c10734 unsat10734 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1714 := h 1713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10735 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1705, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10735 : lratChecker f10735 p10735 = .success := by decide +kernel
theorem unsat10735 : Unsatisfiable (PosFin 65) f10735 := by
  apply lratCheckerSound f10735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10735
  · intro a ha; simp [p10735] at ha; subst a; trivial
  · exact checked10735
theorem derived10735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10735 := by
  apply localUnsat_implies_entails f10735 [c9748, c1705] c10735 unsat10735 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1705 := h 1704 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10736 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1913, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10736 : lratChecker f10736 p10736 = .success := by decide +kernel
theorem unsat10736 : Unsatisfiable (PosFin 65) f10736 := by
  apply lratCheckerSound f10736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10736
  · intro a ha; simp [p10736] at ha; subst a; trivial
  · exact checked10736
theorem derived10736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10736 := by
  apply localUnsat_implies_entails f10736 [c9748, c1913] c10736 unsat10736 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1913 := h 1912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10737 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2048, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10737 : lratChecker f10737 p10737 = .success := by decide +kernel
theorem unsat10737 : Unsatisfiable (PosFin 65) f10737 := by
  apply lratCheckerSound f10737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10737
  · intro a ha; simp [p10737] at ha; subst a; trivial
  · exact checked10737
theorem derived10737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10737 := by
  apply localUnsat_implies_entails f10737 [c9748, c2048] c10737 unsat10737 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2048 := h 2047 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10738 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1867, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10738 : lratChecker f10738 p10738 = .success := by decide +kernel
theorem unsat10738 : Unsatisfiable (PosFin 65) f10738 := by
  apply lratCheckerSound f10738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10738
  · intro a ha; simp [p10738] at ha; subst a; trivial
  · exact checked10738
theorem derived10738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10738 := by
  apply localUnsat_implies_entails f10738 [c9748, c1867] c10738 unsat10738 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1867 := h 1866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10739 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2229, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p10739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10739 : lratChecker f10739 p10739 = .success := by decide +kernel
theorem unsat10739 : Unsatisfiable (PosFin 65) f10739 := by
  apply lratCheckerSound f10739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10739
  · intro a ha; simp [p10739] at ha; subst a; trivial
  · exact checked10739
theorem derived10739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10739 := by
  apply localUnsat_implies_entails f10739 [c9748, c2229] c10739 unsat10739 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2229 := h 2228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10740 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2225, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10740 : lratChecker f10740 p10740 = .success := by decide +kernel
theorem unsat10740 : Unsatisfiable (PosFin 65) f10740 := by
  apply lratCheckerSound f10740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10740
  · intro a ha; simp [p10740] at ha; subst a; trivial
  · exact checked10740
theorem derived10740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10740 := by
  apply localUnsat_implies_entails f10740 [c9748, c2225] c10740 unsat10740 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2225 := h 2224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10741 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2340, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p10741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10741 : lratChecker f10741 p10741 = .success := by decide +kernel
theorem unsat10741 : Unsatisfiable (PosFin 65) f10741 := by
  apply lratCheckerSound f10741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10741
  · intro a ha; simp [p10741] at ha; subst a; trivial
  · exact checked10741
theorem derived10741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10741 := by
  apply localUnsat_implies_entails f10741 [c9748, c2340] c10741 unsat10741 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2340 := h 2339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10742 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2194, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10742 : lratChecker f10742 p10742 = .success := by decide +kernel
theorem unsat10742 : Unsatisfiable (PosFin 65) f10742 := by
  apply lratCheckerSound f10742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10742
  · intro a ha; simp [p10742] at ha; subst a; trivial
  · exact checked10742
theorem derived10742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10742 := by
  apply localUnsat_implies_entails f10742 [c9748, c2194] c10742 unsat10742 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2194 := h 2193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10743 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1687, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10743 : lratChecker f10743 p10743 = .success := by decide +kernel
theorem unsat10743 : Unsatisfiable (PosFin 65) f10743 := by
  apply lratCheckerSound f10743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10743
  · intro a ha; simp [p10743] at ha; subst a; trivial
  · exact checked10743
theorem derived10743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10743 := by
  apply localUnsat_implies_entails f10743 [c9748, c1687] c10743 unsat10743 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1687 := h 1686 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10744 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1610, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10744 : lratChecker f10744 p10744 = .success := by decide +kernel
theorem unsat10744 : Unsatisfiable (PosFin 65) f10744 := by
  apply lratCheckerSound f10744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10744
  · intro a ha; simp [p10744] at ha; subst a; trivial
  · exact checked10744
theorem derived10744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10744 := by
  apply localUnsat_implies_entails f10744 [c9748, c1610] c10744 unsat10744 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1610 := h 1609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10745 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1841, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10745 : lratChecker f10745 p10745 = .success := by decide +kernel
theorem unsat10745 : Unsatisfiable (PosFin 65) f10745 := by
  apply lratCheckerSound f10745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10745
  · intro a ha; simp [p10745] at ha; subst a; trivial
  · exact checked10745
theorem derived10745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10745 := by
  apply localUnsat_implies_entails f10745 [c9748, c1841] c10745 unsat10745 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1841 := h 1840 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10746 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨56, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2238, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10746 : lratChecker f10746 p10746 = .success := by decide +kernel
theorem unsat10746 : Unsatisfiable (PosFin 65) f10746 := by
  apply lratCheckerSound f10746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10746
  · intro a ha; simp [p10746] at ha; subst a; trivial
  · exact checked10746
theorem derived10746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10746 := by
  apply localUnsat_implies_entails f10746 [c9748, c2238] c10746 unsat10746 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2238 := h 2237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10747 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2242, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10747 : lratChecker f10747 p10747 = .success := by decide +kernel
theorem unsat10747 : Unsatisfiable (PosFin 65) f10747 := by
  apply lratCheckerSound f10747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10747
  · intro a ha; simp [p10747] at ha; subst a; trivial
  · exact checked10747
theorem derived10747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10747 := by
  apply localUnsat_implies_entails f10747 [c9748, c2242] c10747 unsat10747 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2242 := h 2241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10748 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2181, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10748 : lratChecker f10748 p10748 = .success := by decide +kernel
theorem unsat10748 : Unsatisfiable (PosFin 65) f10748 := by
  apply lratCheckerSound f10748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10748
  · intro a ha; simp [p10748] at ha; subst a; trivial
  · exact checked10748
theorem derived10748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10748 := by
  apply localUnsat_implies_entails f10748 [c9748, c2181] c10748 unsat10748 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2181 := h 2180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10749 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨14, by decide⟩, true), (⟨61, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1821, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true))]
def p10749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10749 : lratChecker f10749 p10749 = .success := by decide +kernel
theorem unsat10749 : Unsatisfiable (PosFin 65) f10749 := by
  apply lratCheckerSound f10749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10749
  · intro a ha; simp [p10749] at ha; subst a; trivial
  · exact checked10749
theorem derived10749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10749 := by
  apply localUnsat_implies_entails f10749 [c9748, c1821] c10749 unsat10749 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1821 := h 1820 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10750 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨14, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2371, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10750 : lratChecker f10750 p10750 = .success := by decide +kernel
theorem unsat10750 : Unsatisfiable (PosFin 65) f10750 := by
  apply lratCheckerSound f10750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10750
  · intro a ha; simp [p10750] at ha; subst a; trivial
  · exact checked10750
theorem derived10750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10750 := by
  apply localUnsat_implies_entails f10750 [c9748, c2371] c10750 unsat10750 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2371 := h 2370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10750

end CochromaticTwenty.Certificates.FixedCore0
