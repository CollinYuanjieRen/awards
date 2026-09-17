import MerLeanExperiment.Certificates.FixedCore0.Steps2800_2899

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10451 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10451 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2203, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10451 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10451 : lratChecker f10451 p10451 = .success := by decide +kernel
theorem unsat10451 : Unsatisfiable (PosFin 65) f10451 := by
  apply lratCheckerSound f10451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10451
  · intro a ha; simp [p10451] at ha; subst a; trivial
  · exact checked10451
theorem derived10451 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10451 := by
  apply localUnsat_implies_entails f10451 [c9748, c2203] c10451 unsat10451 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2203 := h 2202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10452 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10452 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2343, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10452 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10452 : lratChecker f10452 p10452 = .success := by decide +kernel
theorem unsat10452 : Unsatisfiable (PosFin 65) f10452 := by
  apply lratCheckerSound f10452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10452
  · intro a ha; simp [p10452] at ha; subst a; trivial
  · exact checked10452
theorem derived10452 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10452 := by
  apply localUnsat_implies_entails f10452 [c9748, c2343] c10452 unsat10452 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2343 := h 2342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10453 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10453 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1760, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10453 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10453 : lratChecker f10453 p10453 = .success := by decide +kernel
theorem unsat10453 : Unsatisfiable (PosFin 65) f10453 := by
  apply lratCheckerSound f10453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10453
  · intro a ha; simp [p10453] at ha; subst a; trivial
  · exact checked10453
theorem derived10453 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10453 := by
  apply localUnsat_implies_entails f10453 [c9748, c1760] c10453 unsat10453 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1760 := h 1759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10454 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10454 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1623, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10454 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10454 : lratChecker f10454 p10454 = .success := by decide +kernel
theorem unsat10454 : Unsatisfiable (PosFin 65) f10454 := by
  apply lratCheckerSound f10454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10454
  · intro a ha; simp [p10454] at ha; subst a; trivial
  · exact checked10454
theorem derived10454 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10454 := by
  apply localUnsat_implies_entails f10454 [c9748, c1623] c10454 unsat10454 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1623 := h 1622 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10455 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10455 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1614, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10455 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10455 : lratChecker f10455 p10455 = .success := by decide +kernel
theorem unsat10455 : Unsatisfiable (PosFin 65) f10455 := by
  apply lratCheckerSound f10455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10455
  · intro a ha; simp [p10455] at ha; subst a; trivial
  · exact checked10455
theorem derived10455 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10455 := by
  apply localUnsat_implies_entails f10455 [c9748, c1614] c10455 unsat10455 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1614 := h 1613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10456 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10456 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2046, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p10456 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10456 : lratChecker f10456 p10456 = .success := by decide +kernel
theorem unsat10456 : Unsatisfiable (PosFin 65) f10456 := by
  apply lratCheckerSound f10456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10456
  · intro a ha; simp [p10456] at ha; subst a; trivial
  · exact checked10456
theorem derived10456 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10456 := by
  apply localUnsat_implies_entails f10456 [c9748, c2046] c10456 unsat10456 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2046 := h 2045 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10457 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10457 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1704, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p10457 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10457 : lratChecker f10457 p10457 = .success := by decide +kernel
theorem unsat10457 : Unsatisfiable (PosFin 65) f10457 := by
  apply lratCheckerSound f10457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10457
  · intro a ha; simp [p10457] at ha; subst a; trivial
  · exact checked10457
theorem derived10457 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10457 := by
  apply localUnsat_implies_entails f10457 [c9748, c1704] c10457 unsat10457 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1704 := h 1703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10458 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10458 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1468, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10458 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10458 : lratChecker f10458 p10458 = .success := by decide +kernel
theorem unsat10458 : Unsatisfiable (PosFin 65) f10458 := by
  apply lratCheckerSound f10458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10458
  · intro a ha; simp [p10458] at ha; subst a; trivial
  · exact checked10458
theorem derived10458 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10458 := by
  apply localUnsat_implies_entails f10458 [c9748, c1468] c10458 unsat10458 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1468 := h 1467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10459 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10459 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1838, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10459 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10459 : lratChecker f10459 p10459 = .success := by decide +kernel
theorem unsat10459 : Unsatisfiable (PosFin 65) f10459 := by
  apply lratCheckerSound f10459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10459
  · intro a ha; simp [p10459] at ha; subst a; trivial
  · exact checked10459
theorem derived10459 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10459 := by
  apply localUnsat_implies_entails f10459 [c9748, c1838] c10459 unsat10459 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1838 := h 1837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10460 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10460 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2193, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p10460 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10460 : lratChecker f10460 p10460 = .success := by decide +kernel
theorem unsat10460 : Unsatisfiable (PosFin 65) f10460 := by
  apply lratCheckerSound f10460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10460
  · intro a ha; simp [p10460] at ha; subst a; trivial
  · exact checked10460
theorem derived10460 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10460 := by
  apply localUnsat_implies_entails f10460 [c9748, c2193] c10460 unsat10460 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2193 := h 2192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10461 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10461 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1607, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10461 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10461 : lratChecker f10461 p10461 = .success := by decide +kernel
theorem unsat10461 : Unsatisfiable (PosFin 65) f10461 := by
  apply lratCheckerSound f10461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10461
  · intro a ha; simp [p10461] at ha; subst a; trivial
  · exact checked10461
theorem derived10461 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10461 := by
  apply localUnsat_implies_entails f10461 [c9748, c1607] c10461 unsat10461 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1607 := h 1606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10462 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10462 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1615, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10462 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10462 : lratChecker f10462 p10462 = .success := by decide +kernel
theorem unsat10462 : Unsatisfiable (PosFin 65) f10462 := by
  apply lratCheckerSound f10462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10462
  · intro a ha; simp [p10462] at ha; subst a; trivial
  · exact checked10462
theorem derived10462 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10462 := by
  apply localUnsat_implies_entails f10462 [c9748, c1615] c10462 unsat10462 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1615 := h 1614 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10463 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10463 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1845, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10463 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10463 : lratChecker f10463 p10463 = .success := by decide +kernel
theorem unsat10463 : Unsatisfiable (PosFin 65) f10463 := by
  apply lratCheckerSound f10463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10463
  · intro a ha; simp [p10463] at ha; subst a; trivial
  · exact checked10463
theorem derived10463 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10463 := by
  apply localUnsat_implies_entails f10463 [c9748, c1845] c10463 unsat10463 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1845 := h 1844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10464 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10464 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1700, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10464 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10464 : lratChecker f10464 p10464 = .success := by decide +kernel
theorem unsat10464 : Unsatisfiable (PosFin 65) f10464 := by
  apply lratCheckerSound f10464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10464
  · intro a ha; simp [p10464] at ha; subst a; trivial
  · exact checked10464
theorem derived10464 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10464 := by
  apply localUnsat_implies_entails f10464 [c9748, c1700] c10464 unsat10464 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1700 := h 1699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10465 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨58, by decide⟩, false), (⟨16, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10465 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1606, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10465 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10465 : lratChecker f10465 p10465 = .success := by decide +kernel
theorem unsat10465 : Unsatisfiable (PosFin 65) f10465 := by
  apply lratCheckerSound f10465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10465
  · intro a ha; simp [p10465] at ha; subst a; trivial
  · exact checked10465
theorem derived10465 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10465 := by
  apply localUnsat_implies_entails f10465 [c9748, c1606] c10465 unsat10465 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1606 := h 1605 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10466 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10466 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1681, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10466 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10466 : lratChecker f10466 p10466 = .success := by decide +kernel
theorem unsat10466 : Unsatisfiable (PosFin 65) f10466 := by
  apply lratCheckerSound f10466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10466
  · intro a ha; simp [p10466] at ha; subst a; trivial
  · exact checked10466
theorem derived10466 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10466 := by
  apply localUnsat_implies_entails f10466 [c9748, c1681] c10466 unsat10466 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1681 := h 1680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10467 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10467 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1717, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p10467 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10467 : lratChecker f10467 p10467 = .success := by decide +kernel
theorem unsat10467 : Unsatisfiable (PosFin 65) f10467 := by
  apply lratCheckerSound f10467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10467
  · intro a ha; simp [p10467] at ha; subst a; trivial
  · exact checked10467
theorem derived10467 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10467 := by
  apply localUnsat_implies_entails f10467 [c9748, c1717] c10467 unsat10467 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1717 := h 1716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10468 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨58, by decide⟩, false), (⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10468 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1463, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10468 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10468 : lratChecker f10468 p10468 = .success := by decide +kernel
theorem unsat10468 : Unsatisfiable (PosFin 65) f10468 := by
  apply lratCheckerSound f10468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10468
  · intro a ha; simp [p10468] at ha; subst a; trivial
  · exact checked10468
theorem derived10468 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10468 := by
  apply localUnsat_implies_entails f10468 [c9748, c1463] c10468 unsat10468 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1463 := h 1462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10469 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨58, by decide⟩, false), (⟨8, by decide⟩, true), (⟨57, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10469 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1680, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10469 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10469 : lratChecker f10469 p10469 = .success := by decide +kernel
theorem unsat10469 : Unsatisfiable (PosFin 65) f10469 := by
  apply lratCheckerSound f10469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10469
  · intro a ha; simp [p10469] at ha; subst a; trivial
  · exact checked10469
theorem derived10469 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10469 := by
  apply localUnsat_implies_entails f10469 [c9748, c1680] c10469 unsat10469 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1680 := h 1679 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10470 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10470 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1713, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p10470 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10470 : lratChecker f10470 p10470 = .success := by decide +kernel
theorem unsat10470 : Unsatisfiable (PosFin 65) f10470 := by
  apply lratCheckerSound f10470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10470
  · intro a ha; simp [p10470] at ha; subst a; trivial
  · exact checked10470
theorem derived10470 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10470 := by
  apply localUnsat_implies_entails f10470 [c9748, c1713] c10470 unsat10470 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1713 := h 1712 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10471 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨13, by decide⟩, true), (⟨58, by decide⟩, false), (⟨14, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10471 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2190, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10471 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10471 : lratChecker f10471 p10471 = .success := by decide +kernel
theorem unsat10471 : Unsatisfiable (PosFin 65) f10471 := by
  apply lratCheckerSound f10471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10471
  · intro a ha; simp [p10471] at ha; subst a; trivial
  · exact checked10471
theorem derived10471 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10471 := by
  apply localUnsat_implies_entails f10471 [c9748, c2190] c10471 unsat10471 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2190 := h 2189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10472 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10472 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1774, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p10472 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10472 : lratChecker f10472 p10472 = .success := by decide +kernel
theorem unsat10472 : Unsatisfiable (PosFin 65) f10472 := by
  apply lratCheckerSound f10472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10472
  · intro a ha; simp [p10472] at ha; subst a; trivial
  · exact checked10472
theorem derived10472 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10472 := by
  apply localUnsat_implies_entails f10472 [c9748, c1774] c10472 unsat10472 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1774 := h 1773 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10473 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨58, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10473 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2188, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10473 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10473 : lratChecker f10473 p10473 = .success := by decide +kernel
theorem unsat10473 : Unsatisfiable (PosFin 65) f10473 := by
  apply lratCheckerSound f10473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10473
  · intro a ha; simp [p10473] at ha; subst a; trivial
  · exact checked10473
theorem derived10473 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10473 := by
  apply localUnsat_implies_entails f10473 [c9748, c2188] c10473 unsat10473 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2188 := h 2187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10474 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨58, by decide⟩, false), (⟨13, by decide⟩, true), (⟨26, by decide⟩, false), (⟨57, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10474 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2189, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10474 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10474 : lratChecker f10474 p10474 = .success := by decide +kernel
theorem unsat10474 : Unsatisfiable (PosFin 65) f10474 := by
  apply lratCheckerSound f10474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10474
  · intro a ha; simp [p10474] at ha; subst a; trivial
  · exact checked10474
theorem derived10474 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10474 := by
  apply localUnsat_implies_entails f10474 [c9748, c2189] c10474 unsat10474 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2189 := h 2188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10475 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10475 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1554, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p10475 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10475 : lratChecker f10475 p10475 = .success := by decide +kernel
theorem unsat10475 : Unsatisfiable (PosFin 65) f10475 := by
  apply lratCheckerSound f10475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10475
  · intro a ha; simp [p10475] at ha; subst a; trivial
  · exact checked10475
theorem derived10475 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10475 := by
  apply localUnsat_implies_entails f10475 [c9748, c1554] c10475 unsat10475 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1554 := h 1553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10476 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨26, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10476 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2056, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10476 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10476 : lratChecker f10476 p10476 = .success := by decide +kernel
theorem unsat10476 : Unsatisfiable (PosFin 65) f10476 := by
  apply lratCheckerSound f10476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10476
  · intro a ha; simp [p10476] at ha; subst a; trivial
  · exact checked10476
theorem derived10476 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10476 := by
  apply localUnsat_implies_entails f10476 [c9748, c2056] c10476 unsat10476 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2056 := h 2055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10477 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨57, by decide⟩, false), (⟨58, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10477 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1604, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, true))]
def p10477 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10477 : lratChecker f10477 p10477 = .success := by decide +kernel
theorem unsat10477 : Unsatisfiable (PosFin 65) f10477 := by
  apply lratCheckerSound f10477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10477
  · intro a ha; simp [p10477] at ha; subst a; trivial
  · exact checked10477
theorem derived10477 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10477 := by
  apply localUnsat_implies_entails f10477 [c9748, c1604] c10477 unsat10477 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1604 := h 1603 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10478 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10478 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1869, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10478 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10478 : lratChecker f10478 p10478 = .success := by decide +kernel
theorem unsat10478 : Unsatisfiable (PosFin 65) f10478 := by
  apply lratCheckerSound f10478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10478
  · intro a ha; simp [p10478] at ha; subst a; trivial
  · exact checked10478
theorem derived10478 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10478 := by
  apply localUnsat_implies_entails f10478 [c9748, c1869] c10478 unsat10478 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1869 := h 1868 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10479 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10479 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1553, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10479 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10479 : lratChecker f10479 p10479 = .success := by decide +kernel
theorem unsat10479 : Unsatisfiable (PosFin 65) f10479 := by
  apply lratCheckerSound f10479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10479
  · intro a ha; simp [p10479] at ha; subst a; trivial
  · exact checked10479
theorem derived10479 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10479 := by
  apply localUnsat_implies_entails f10479 [c9748, c1553] c10479 unsat10479 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1553 := h 1552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10480 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10480 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1701, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p10480 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10480 : lratChecker f10480 p10480 = .success := by decide +kernel
theorem unsat10480 : Unsatisfiable (PosFin 65) f10480 := by
  apply lratCheckerSound f10480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10480
  · intro a ha; simp [p10480] at ha; subst a; trivial
  · exact checked10480
theorem derived10480 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10480 := by
  apply localUnsat_implies_entails f10480 [c9748, c1701] c10480 unsat10480 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1701 := h 1700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10481 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1772, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10481 : lratChecker f10481 p10481 = .success := by decide +kernel
theorem unsat10481 : Unsatisfiable (PosFin 65) f10481 := by
  apply lratCheckerSound f10481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10481
  · intro a ha; simp [p10481] at ha; subst a; trivial
  · exact checked10481
theorem derived10481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10481 := by
  apply localUnsat_implies_entails f10481 [c9748, c1772] c10481 unsat10481 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1772 := h 1771 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10482 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2047, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10482 : lratChecker f10482 p10482 = .success := by decide +kernel
theorem unsat10482 : Unsatisfiable (PosFin 65) f10482 := by
  apply lratCheckerSound f10482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10482
  · intro a ha; simp [p10482] at ha; subst a; trivial
  · exact checked10482
theorem derived10482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10482 := by
  apply localUnsat_implies_entails f10482 [c9748, c2047] c10482 unsat10482 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2047 := h 2046 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10483 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2211, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p10483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10483 : lratChecker f10483 p10483 = .success := by decide +kernel
theorem unsat10483 : Unsatisfiable (PosFin 65) f10483 := by
  apply lratCheckerSound f10483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10483
  · intro a ha; simp [p10483] at ha; subst a; trivial
  · exact checked10483
theorem derived10483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10483 := by
  apply localUnsat_implies_entails f10483 [c9748, c2211] c10483 unsat10483 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2211 := h 2210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10484 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1782, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p10484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10484 : lratChecker f10484 p10484 = .success := by decide +kernel
theorem unsat10484 : Unsatisfiable (PosFin 65) f10484 := by
  apply lratCheckerSound f10484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10484
  · intro a ha; simp [p10484] at ha; subst a; trivial
  · exact checked10484
theorem derived10484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10484 := by
  apply localUnsat_implies_entails f10484 [c9748, c1782] c10484 unsat10484 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1782 := h 1781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10485 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2052, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p10485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10485 : lratChecker f10485 p10485 = .success := by decide +kernel
theorem unsat10485 : Unsatisfiable (PosFin 65) f10485 := by
  apply lratCheckerSound f10485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10485
  · intro a ha; simp [p10485] at ha; subst a; trivial
  · exact checked10485
theorem derived10485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10485 := by
  apply localUnsat_implies_entails f10485 [c9748, c2052] c10485 unsat10485 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2052 := h 2051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10486 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2219, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10486 : lratChecker f10486 p10486 = .success := by decide +kernel
theorem unsat10486 : Unsatisfiable (PosFin 65) f10486 := by
  apply lratCheckerSound f10486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10486
  · intro a ha; simp [p10486] at ha; subst a; trivial
  · exact checked10486
theorem derived10486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10486 := by
  apply localUnsat_implies_entails f10486 [c9748, c2219] c10486 unsat10486 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2219 := h 2218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10487 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2303, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p10487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10487 : lratChecker f10487 p10487 = .success := by decide +kernel
theorem unsat10487 : Unsatisfiable (PosFin 65) f10487 := by
  apply lratCheckerSound f10487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10487
  · intro a ha; simp [p10487] at ha; subst a; trivial
  · exact checked10487
theorem derived10487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10487 := by
  apply localUnsat_implies_entails f10487 [c9748, c2303] c10487 unsat10487 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2303 := h 2302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10488 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨58, by decide⟩, false), (⟨13, by decide⟩, true), (⟨60, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1973, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true))]
def p10488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10488 : lratChecker f10488 p10488 = .success := by decide +kernel
theorem unsat10488 : Unsatisfiable (PosFin 65) f10488 := by
  apply lratCheckerSound f10488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10488
  · intro a ha; simp [p10488] at ha; subst a; trivial
  · exact checked10488
theorem derived10488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10488 := by
  apply localUnsat_implies_entails f10488 [c9748, c1973] c10488 unsat10488 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1973 := h 1972 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10489 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1997, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p10489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10489 : lratChecker f10489 p10489 = .success := by decide +kernel
theorem unsat10489 : Unsatisfiable (PosFin 65) f10489 := by
  apply lratCheckerSound f10489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10489
  · intro a ha; simp [p10489] at ha; subst a; trivial
  · exact checked10489
theorem derived10489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10489 := by
  apply localUnsat_implies_entails f10489 [c9748, c1997] c10489 unsat10489 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1997 := h 1996 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10490 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨16, by decide⟩, true), (⟨26, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2312, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10490 : lratChecker f10490 p10490 = .success := by decide +kernel
theorem unsat10490 : Unsatisfiable (PosFin 65) f10490 := by
  apply lratCheckerSound f10490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10490
  · intro a ha; simp [p10490] at ha; subst a; trivial
  · exact checked10490
theorem derived10490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10490 := by
  apply localUnsat_implies_entails f10490 [c9748, c2312] c10490 unsat10490 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2312 := h 2311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10491 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1991, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10491 : lratChecker f10491 p10491 = .success := by decide +kernel
theorem unsat10491 : Unsatisfiable (PosFin 65) f10491 := by
  apply lratCheckerSound f10491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10491
  · intro a ha; simp [p10491] at ha; subst a; trivial
  · exact checked10491
theorem derived10491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10491 := by
  apply localUnsat_implies_entails f10491 [c9748, c1991] c10491 unsat10491 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1991 := h 1990 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10492 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2055, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10492 : lratChecker f10492 p10492 = .success := by decide +kernel
theorem unsat10492 : Unsatisfiable (PosFin 65) f10492 := by
  apply lratCheckerSound f10492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10492
  · intro a ha; simp [p10492] at ha; subst a; trivial
  · exact checked10492
theorem derived10492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10492 := by
  apply localUnsat_implies_entails f10492 [c9748, c2055] c10492 unsat10492 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2055 := h 2054 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10493 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1711, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p10493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10493 : lratChecker f10493 p10493 = .success := by decide +kernel
theorem unsat10493 : Unsatisfiable (PosFin 65) f10493 := by
  apply lratCheckerSound f10493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10493
  · intro a ha; simp [p10493] at ha; subst a; trivial
  · exact checked10493
theorem derived10493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10493 := by
  apply localUnsat_implies_entails f10493 [c9748, c1711] c10493 unsat10493 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1711 := h 1710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10494 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2308, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10494 : lratChecker f10494 p10494 = .success := by decide +kernel
theorem unsat10494 : Unsatisfiable (PosFin 65) f10494 := by
  apply lratCheckerSound f10494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10494
  · intro a ha; simp [p10494] at ha; subst a; trivial
  · exact checked10494
theorem derived10494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10494 := by
  apply localUnsat_implies_entails f10494 [c9748, c2308] c10494 unsat10494 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2308 := h 2307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10495 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2309, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10495 : lratChecker f10495 p10495 = .success := by decide +kernel
theorem unsat10495 : Unsatisfiable (PosFin 65) f10495 := by
  apply lratCheckerSound f10495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10495
  · intro a ha; simp [p10495] at ha; subst a; trivial
  · exact checked10495
theorem derived10495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10495 := by
  apply localUnsat_implies_entails f10495 [c9748, c2309] c10495 unsat10495 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2309 := h 2308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10496 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1992, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p10496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10496 : lratChecker f10496 p10496 = .success := by decide +kernel
theorem unsat10496 : Unsatisfiable (PosFin 65) f10496 := by
  apply lratCheckerSound f10496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10496
  · intro a ha; simp [p10496] at ha; subst a; trivial
  · exact checked10496
theorem derived10496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10496 := by
  apply localUnsat_implies_entails f10496 [c9748, c1992] c10496 unsat10496 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1992 := h 1991 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10497 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1775, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10497 : lratChecker f10497 p10497 = .success := by decide +kernel
theorem unsat10497 : Unsatisfiable (PosFin 65) f10497 := by
  apply lratCheckerSound f10497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10497
  · intro a ha; simp [p10497] at ha; subst a; trivial
  · exact checked10497
theorem derived10497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10497 := by
  apply localUnsat_implies_entails f10497 [c9748, c1775] c10497 unsat10497 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1775 := h 1774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10498 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2300, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10498 : lratChecker f10498 p10498 = .success := by decide +kernel
theorem unsat10498 : Unsatisfiable (PosFin 65) f10498 := by
  apply lratCheckerSound f10498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10498
  · intro a ha; simp [p10498] at ha; subst a; trivial
  · exact checked10498
theorem derived10498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10498 := by
  apply localUnsat_implies_entails f10498 [c9748, c2300] c10498 unsat10498 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2300 := h 2299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10499 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2226, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p10499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10499 : lratChecker f10499 p10499 = .success := by decide +kernel
theorem unsat10499 : Unsatisfiable (PosFin 65) f10499 := by
  apply lratCheckerSound f10499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10499
  · intro a ha; simp [p10499] at ha; subst a; trivial
  · exact checked10499
theorem derived10499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10499 := by
  apply localUnsat_implies_entails f10499 [c9748, c2226] c10499 unsat10499 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2226 := h 2225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10500 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2215, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10500 : lratChecker f10500 p10500 = .success := by decide +kernel
theorem unsat10500 : Unsatisfiable (PosFin 65) f10500 := by
  apply lratCheckerSound f10500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10500
  · intro a ha; simp [p10500] at ha; subst a; trivial
  · exact checked10500
theorem derived10500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10500 := by
  apply localUnsat_implies_entails f10500 [c9748, c2215] c10500 unsat10500 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2215 := h 2214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10501 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1870, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p10501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10501 : lratChecker f10501 p10501 = .success := by decide +kernel
theorem unsat10501 : Unsatisfiable (PosFin 65) f10501 := by
  apply lratCheckerSound f10501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10501
  · intro a ha; simp [p10501] at ha; subst a; trivial
  · exact checked10501
theorem derived10501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10501 := by
  apply localUnsat_implies_entails f10501 [c9748, c1870] c10501 unsat10501 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1870 := h 1869 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10502 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2053, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10502 : lratChecker f10502 p10502 = .success := by decide +kernel
theorem unsat10502 : Unsatisfiable (PosFin 65) f10502 := by
  apply lratCheckerSound f10502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10502
  · intro a ha; simp [p10502] at ha; subst a; trivial
  · exact checked10502
theorem derived10502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10502 := by
  apply localUnsat_implies_entails f10502 [c9748, c2053] c10502 unsat10502 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2053 := h 2052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10503 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2222, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p10503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10503 : lratChecker f10503 p10503 = .success := by decide +kernel
theorem unsat10503 : Unsatisfiable (PosFin 65) f10503 := by
  apply lratCheckerSound f10503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10503
  · intro a ha; simp [p10503] at ha; subst a; trivial
  · exact checked10503
theorem derived10503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10503 := by
  apply localUnsat_implies_entails f10503 [c9748, c2222] c10503 unsat10503 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2222 := h 2221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10504 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨23, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2227, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10504 : lratChecker f10504 p10504 = .success := by decide +kernel
theorem unsat10504 : Unsatisfiable (PosFin 65) f10504 := by
  apply lratCheckerSound f10504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10504
  · intro a ha; simp [p10504] at ha; subst a; trivial
  · exact checked10504
theorem derived10504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10504 := by
  apply localUnsat_implies_entails f10504 [c9748, c2227] c10504 unsat10504 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2227 := h 2226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10505 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2345, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10505 : lratChecker f10505 p10505 = .success := by decide +kernel
theorem unsat10505 : Unsatisfiable (PosFin 65) f10505 := by
  apply lratCheckerSound f10505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10505
  · intro a ha; simp [p10505] at ha; subst a; trivial
  · exact checked10505
theorem derived10505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10505 := by
  apply localUnsat_implies_entails f10505 [c9748, c2345] c10505 unsat10505 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2345 := h 2344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10506 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1994, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p10506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10506 : lratChecker f10506 p10506 = .success := by decide +kernel
theorem unsat10506 : Unsatisfiable (PosFin 65) f10506 := by
  apply lratCheckerSound f10506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10506
  · intro a ha; simp [p10506] at ha; subst a; trivial
  · exact checked10506
theorem derived10506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10506 := by
  apply localUnsat_implies_entails f10506 [c9748, c1994] c10506 unsat10506 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1994 := h 1993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10507 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1548, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10507 : lratChecker f10507 p10507 = .success := by decide +kernel
theorem unsat10507 : Unsatisfiable (PosFin 65) f10507 := by
  apply lratCheckerSound f10507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10507
  · intro a ha; simp [p10507] at ha; subst a; trivial
  · exact checked10507
theorem derived10507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10507 := by
  apply localUnsat_implies_entails f10507 [c9748, c1548] c10507 unsat10507 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1548 := h 1547 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10508 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1921, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10508 : lratChecker f10508 p10508 = .success := by decide +kernel
theorem unsat10508 : Unsatisfiable (PosFin 65) f10508 := by
  apply lratCheckerSound f10508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10508
  · intro a ha; simp [p10508] at ha; subst a; trivial
  · exact checked10508
theorem derived10508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10508 := by
  apply localUnsat_implies_entails f10508 [c9748, c1921] c10508 unsat10508 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1921 := h 1920 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10509 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2195, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10509 : lratChecker f10509 p10509 = .success := by decide +kernel
theorem unsat10509 : Unsatisfiable (PosFin 65) f10509 := by
  apply lratCheckerSound f10509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10509
  · intro a ha; simp [p10509] at ha; subst a; trivial
  · exact checked10509
theorem derived10509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10509 := by
  apply localUnsat_implies_entails f10509 [c9748, c2195] c10509 unsat10509 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2195 := h 2194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10510 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1684, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p10510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10510 : lratChecker f10510 p10510 = .success := by decide +kernel
theorem unsat10510 : Unsatisfiable (PosFin 65) f10510 := by
  apply lratCheckerSound f10510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10510
  · intro a ha; simp [p10510] at ha; subst a; trivial
  · exact checked10510
theorem derived10510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10510 := by
  apply localUnsat_implies_entails f10510 [c9748, c1684] c10510 unsat10510 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1684 := h 1683 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10511 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1761, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p10511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10511 : lratChecker f10511 p10511 = .success := by decide +kernel
theorem unsat10511 : Unsatisfiable (PosFin 65) f10511 := by
  apply lratCheckerSound f10511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10511
  · intro a ha; simp [p10511] at ha; subst a; trivial
  · exact checked10511
theorem derived10511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10511 := by
  apply localUnsat_implies_entails f10511 [c9748, c1761] c10511 unsat10511 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1761 := h 1760 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10512 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1466, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10512 : lratChecker f10512 p10512 = .success := by decide +kernel
theorem unsat10512 : Unsatisfiable (PosFin 65) f10512 := by
  apply lratCheckerSound f10512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10512
  · intro a ha; simp [p10512] at ha; subst a; trivial
  · exact checked10512
theorem derived10512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10512 := by
  apply localUnsat_implies_entails f10512 [c9748, c1466] c10512 unsat10512 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1466 := h 1465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10513 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1467, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10513 : lratChecker f10513 p10513 = .success := by decide +kernel
theorem unsat10513 : Unsatisfiable (PosFin 65) f10513 := by
  apply lratCheckerSound f10513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10513
  · intro a ha; simp [p10513] at ha; subst a; trivial
  · exact checked10513
theorem derived10513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10513 := by
  apply localUnsat_implies_entails f10513 [c9748, c1467] c10513 unsat10513 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1467 := h 1466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10514 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2192, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10514 : lratChecker f10514 p10514 = .success := by decide +kernel
theorem unsat10514 : Unsatisfiable (PosFin 65) f10514 := by
  apply lratCheckerSound f10514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10514
  · intro a ha; simp [p10514] at ha; subst a; trivial
  · exact checked10514
theorem derived10514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10514 := by
  apply localUnsat_implies_entails f10514 [c9748, c2192] c10514 unsat10514 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2192 := h 2191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10515 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2037, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10515 : lratChecker f10515 p10515 = .success := by decide +kernel
theorem unsat10515 : Unsatisfiable (PosFin 65) f10515 := by
  apply lratCheckerSound f10515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10515
  · intro a ha; simp [p10515] at ha; subst a; trivial
  · exact checked10515
theorem derived10515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10515 := by
  apply localUnsat_implies_entails f10515 [c9748, c2037] c10515 unsat10515 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2037 := h 2036 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10516 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2054, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p10516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10516 : lratChecker f10516 p10516 = .success := by decide +kernel
theorem unsat10516 : Unsatisfiable (PosFin 65) f10516 := by
  apply lratCheckerSound f10516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10516
  · intro a ha; simp [p10516] at ha; subst a; trivial
  · exact checked10516
theorem derived10516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10516 := by
  apply localUnsat_implies_entails f10516 [c9748, c2054] c10516 unsat10516 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2054 := h 2053 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10517 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1689, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p10517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10517 : lratChecker f10517 p10517 = .success := by decide +kernel
theorem unsat10517 : Unsatisfiable (PosFin 65) f10517 := by
  apply lratCheckerSound f10517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10517
  · intro a ha; simp [p10517] at ha; subst a; trivial
  · exact checked10517
theorem derived10517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10517 := by
  apply localUnsat_implies_entails f10517 [c9748, c1689] c10517 unsat10517 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1689 := h 1688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10518 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1976, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p10518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10518 : lratChecker f10518 p10518 = .success := by decide +kernel
theorem unsat10518 : Unsatisfiable (PosFin 65) f10518 := by
  apply lratCheckerSound f10518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10518
  · intro a ha; simp [p10518] at ha; subst a; trivial
  · exact checked10518
theorem derived10518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10518 := by
  apply localUnsat_implies_entails f10518 [c9748, c1976] c10518 unsat10518 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1976 := h 1975 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10519 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨64, by decide⟩, true), (⟨54, by decide⟩, true), (⟨7, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1964, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10519 : lratChecker f10519 p10519 = .success := by decide +kernel
theorem unsat10519 : Unsatisfiable (PosFin 65) f10519 := by
  apply lratCheckerSound f10519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10519
  · intro a ha; simp [p10519] at ha; subst a; trivial
  · exact checked10519
theorem derived10519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10519 := by
  apply localUnsat_implies_entails f10519 [c9748, c1964] c10519 unsat10519 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1964 := h 1963 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10520 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨60, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1812, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10520 : lratChecker f10520 p10520 = .success := by decide +kernel
theorem unsat10520 : Unsatisfiable (PosFin 65) f10520 := by
  apply lratCheckerSound f10520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10520
  · intro a ha; simp [p10520] at ha; subst a; trivial
  · exact checked10520
theorem derived10520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10520 := by
  apply localUnsat_implies_entails f10520 [c9748, c1812] c10520 unsat10520 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1812 := h 1811 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10521 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨64, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2260, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10521 : lratChecker f10521 p10521 = .success := by decide +kernel
theorem unsat10521 : Unsatisfiable (PosFin 65) f10521 := by
  apply lratCheckerSound f10521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10521
  · intro a ha; simp [p10521] at ha; subst a; trivial
  · exact checked10521
theorem derived10521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10521 := by
  apply localUnsat_implies_entails f10521 [c9748, c2260] c10521 unsat10521 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2260 := h 2259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10522 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨57, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2067, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p10522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10522 : lratChecker f10522 p10522 = .success := by decide +kernel
theorem unsat10522 : Unsatisfiable (PosFin 65) f10522 := by
  apply lratCheckerSound f10522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10522
  · intro a ha; simp [p10522] at ha; subst a; trivial
  · exact checked10522
theorem derived10522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10522 := by
  apply localUnsat_implies_entails f10522 [c9748, c2067] c10522 unsat10522 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2067 := h 2066 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10523 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨60, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2065, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p10523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10523 : lratChecker f10523 p10523 = .success := by decide +kernel
theorem unsat10523 : Unsatisfiable (PosFin 65) f10523 := by
  apply lratCheckerSound f10523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10523
  · intro a ha; simp [p10523] at ha; subst a; trivial
  · exact checked10523
theorem derived10523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10523 := by
  apply localUnsat_implies_entails f10523 [c9748, c2065] c10523 unsat10523 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2065 := h 2064 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10524 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨60, by decide⟩, true), (⟨55, by decide⟩, true), (⟨13, by decide⟩, true), (⟨57, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2266, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false))]
def p10524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10524 : lratChecker f10524 p10524 = .success := by decide +kernel
theorem unsat10524 : Unsatisfiable (PosFin 65) f10524 := by
  apply lratCheckerSound f10524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10524
  · intro a ha; simp [p10524] at ha; subst a; trivial
  · exact checked10524
theorem derived10524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10524 := by
  apply localUnsat_implies_entails f10524 [c9748, c2266] c10524 unsat10524 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2266 := h 2265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10525 : DefaultClause 65 := directClause [(⟨52, by decide⟩, true), (⟨60, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1514, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p10525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10525 : lratChecker f10525 p10525 = .success := by decide +kernel
theorem unsat10525 : Unsatisfiable (PosFin 65) f10525 := by
  apply lratCheckerSound f10525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10525
  · intro a ha; simp [p10525] at ha; subst a; trivial
  · exact checked10525
theorem derived10525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10525 := by
  apply localUnsat_implies_entails f10525 [c9748, c1514] c10525 unsat10525 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1514 := h 1513 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10526 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨60, by decide⟩, true), (⟨59, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1661, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false))]
def p10526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10526 : lratChecker f10526 p10526 = .success := by decide +kernel
theorem unsat10526 : Unsatisfiable (PosFin 65) f10526 := by
  apply lratCheckerSound f10526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10526
  · intro a ha; simp [p10526] at ha; subst a; trivial
  · exact checked10526
theorem derived10526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10526 := by
  apply localUnsat_implies_entails f10526 [c9748, c1661] c10526 unsat10526 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1661 := h 1660 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10527 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨60, by decide⟩, true), (⟨59, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1666, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p10527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10527 : lratChecker f10527 p10527 = .success := by decide +kernel
theorem unsat10527 : Unsatisfiable (PosFin 65) f10527 := by
  apply lratCheckerSound f10527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10527
  · intro a ha; simp [p10527] at ha; subst a; trivial
  · exact checked10527
theorem derived10527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10527 := by
  apply localUnsat_implies_entails f10527 [c9748, c1666] c10527 unsat10527 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1666 := h 1665 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10528 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨52, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1652, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10528 : lratChecker f10528 p10528 = .success := by decide +kernel
theorem unsat10528 : Unsatisfiable (PosFin 65) f10528 := by
  apply lratCheckerSound f10528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10528
  · intro a ha; simp [p10528] at ha; subst a; trivial
  · exact checked10528
theorem derived10528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10528 := by
  apply localUnsat_implies_entails f10528 [c9748, c1652] c10528 unsat10528 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1652 := h 1651 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10529 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨60, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2330, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, false))]
def p10529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10529 : lratChecker f10529 p10529 = .success := by decide +kernel
theorem unsat10529 : Unsatisfiable (PosFin 65) f10529 := by
  apply lratCheckerSound f10529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10529
  · intro a ha; simp [p10529] at ha; subst a; trivial
  · exact checked10529
theorem derived10529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10529 := by
  apply localUnsat_implies_entails f10529 [c9748, c2330] c10529 unsat10529 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2330 := h 2329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10530 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨62, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1461, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p10530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10530 : lratChecker f10530 p10530 = .success := by decide +kernel
theorem unsat10530 : Unsatisfiable (PosFin 65) f10530 := by
  apply lratCheckerSound f10530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10530
  · intro a ha; simp [p10530] at ha; subst a; trivial
  · exact checked10530
theorem derived10530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10530 := by
  apply localUnsat_implies_entails f10530 [c9748, c1461] c10530 unsat10530 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1461 := h 1460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10531 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨62, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨64, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2069, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, true))]
def p10531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10531 : lratChecker f10531 p10531 = .success := by decide +kernel
theorem unsat10531 : Unsatisfiable (PosFin 65) f10531 := by
  apply lratCheckerSound f10531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10531
  · intro a ha; simp [p10531] at ha; subst a; trivial
  · exact checked10531
theorem derived10531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10531 := by
  apply localUnsat_implies_entails f10531 [c9748, c2069] c10531 unsat10531 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2069 := h 2068 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10532 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨62, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1945, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10532 : lratChecker f10532 p10532 = .success := by decide +kernel
theorem unsat10532 : Unsatisfiable (PosFin 65) f10532 := by
  apply lratCheckerSound f10532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10532
  · intro a ha; simp [p10532] at ha; subst a; trivial
  · exact checked10532
theorem derived10532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10532 := by
  apply localUnsat_implies_entails f10532 [c9748, c1945] c10532 unsat10532 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1945 := h 1944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10533 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨62, by decide⟩, false), (⟨7, by decide⟩, true), (⟨57, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1955, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p10533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10533 : lratChecker f10533 p10533 = .success := by decide +kernel
theorem unsat10533 : Unsatisfiable (PosFin 65) f10533 := by
  apply lratCheckerSound f10533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10533
  · intro a ha; simp [p10533] at ha; subst a; trivial
  · exact checked10533
theorem derived10533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10533 := by
  apply localUnsat_implies_entails f10533 [c9748, c1955] c10533 unsat10533 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1955 := h 1954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10534 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1649, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10534 : lratChecker f10534 p10534 = .success := by decide +kernel
theorem unsat10534 : Unsatisfiable (PosFin 65) f10534 := by
  apply lratCheckerSound f10534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10534
  · intro a ha; simp [p10534] at ha; subst a; trivial
  · exact checked10534
theorem derived10534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10534 := by
  apply localUnsat_implies_entails f10534 [c9748, c1649] c10534 unsat10534 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1649 := h 1648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10535 : DefaultClause 65 := directClause [(⟨62, by decide⟩, false), (⟨5, by decide⟩, true), (⟨60, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1511, some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10535 : lratChecker f10535 p10535 = .success := by decide +kernel
theorem unsat10535 : Unsatisfiable (PosFin 65) f10535 := by
  apply lratCheckerSound f10535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10535
  · intro a ha; simp [p10535] at ha; subst a; trivial
  · exact checked10535
theorem derived10535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10535 := by
  apply localUnsat_implies_entails f10535 [c9748, c1511] c10535 unsat10535 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1511 := h 1510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10536 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨62, by decide⟩, false), (⟨57, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1532, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10536 : lratChecker f10536 p10536 = .success := by decide +kernel
theorem unsat10536 : Unsatisfiable (PosFin 65) f10536 := by
  apply lratCheckerSound f10536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10536
  · intro a ha; simp [p10536] at ha; subst a; trivial
  · exact checked10536
theorem derived10536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10536 := by
  apply localUnsat_implies_entails f10536 [c9748, c1532] c10536 unsat10536 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1532 := h 1531 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10537 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1591, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10537 : lratChecker f10537 p10537 = .success := by decide +kernel
theorem unsat10537 : Unsatisfiable (PosFin 65) f10537 := by
  apply lratCheckerSound f10537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10537
  · intro a ha; simp [p10537] at ha; subst a; trivial
  · exact checked10537
theorem derived10537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10537 := by
  apply localUnsat_implies_entails f10537 [c9748, c1591] c10537 unsat10537 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1591 := h 1590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10538 : DefaultClause 65 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1822, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p10538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10538 : lratChecker f10538 p10538 = .success := by decide +kernel
theorem unsat10538 : Unsatisfiable (PosFin 65) f10538 := by
  apply lratCheckerSound f10538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10538
  · intro a ha; simp [p10538] at ha; subst a; trivial
  · exact checked10538
theorem derived10538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10538 := by
  apply localUnsat_implies_entails f10538 [c9748, c1822] c10538 unsat10538 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1822 := h 1821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10539 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨63, by decide⟩, false), (⟨60, by decide⟩, false), (⟨61, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1912, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10539 : lratChecker f10539 p10539 = .success := by decide +kernel
theorem unsat10539 : Unsatisfiable (PosFin 65) f10539 := by
  apply lratCheckerSound f10539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10539
  · intro a ha; simp [p10539] at ha; subst a; trivial
  · exact checked10539
theorem derived10539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10539 := by
  apply localUnsat_implies_entails f10539 [c9748, c1912] c10539 unsat10539 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1912 := h 1911 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10540 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨16, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1656, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p10540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10540 : lratChecker f10540 p10540 = .success := by decide +kernel
theorem unsat10540 : Unsatisfiable (PosFin 65) f10540 := by
  apply lratCheckerSound f10540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10540
  · intro a ha; simp [p10540] at ha; subst a; trivial
  · exact checked10540
theorem derived10540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10540 := by
  apply localUnsat_implies_entails f10540 [c9748, c1656] c10540 unsat10540 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1656 := h 1655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10541 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨59, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1889, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p10541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10541 : lratChecker f10541 p10541 = .success := by decide +kernel
theorem unsat10541 : Unsatisfiable (PosFin 65) f10541 := by
  apply lratCheckerSound f10541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10541
  · intro a ha; simp [p10541] at ha; subst a; trivial
  · exact checked10541
theorem derived10541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10541 := by
  apply localUnsat_implies_entails f10541 [c9748, c1889] c10541 unsat10541 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1889 := h 1888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10542 : DefaultClause 65 := directClause [(⟨39, by decide⟩, true), (⟨43, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1877, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p10542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10542 : lratChecker f10542 p10542 = .success := by decide +kernel
theorem unsat10542 : Unsatisfiable (PosFin 65) f10542 := by
  apply lratCheckerSound f10542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10542
  · intro a ha; simp [p10542] at ha; subst a; trivial
  · exact checked10542
theorem derived10542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10542 := by
  apply localUnsat_implies_entails f10542 [c9748, c1877] c10542 unsat10542 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1877 := h 1876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10543 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, true), (⟨28, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1630, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10543 : lratChecker f10543 p10543 = .success := by decide +kernel
theorem unsat10543 : Unsatisfiable (PosFin 65) f10543 := by
  apply lratCheckerSound f10543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10543
  · intro a ha; simp [p10543] at ha; subst a; trivial
  · exact checked10543
theorem derived10543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10543 := by
  apply localUnsat_implies_entails f10543 [c9748, c1630] c10543 unsat10543 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1630 := h 1629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10544 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1634, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10544 : lratChecker f10544 p10544 = .success := by decide +kernel
theorem unsat10544 : Unsatisfiable (PosFin 65) f10544 := by
  apply lratCheckerSound f10544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10544
  · intro a ha; simp [p10544] at ha; subst a; trivial
  · exact checked10544
theorem derived10544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10544 := by
  apply localUnsat_implies_entails f10544 [c9748, c1634] c10544 unsat10544 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1634 := h 1633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10545 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1594, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10545 : lratChecker f10545 p10545 = .success := by decide +kernel
theorem unsat10545 : Unsatisfiable (PosFin 65) f10545 := by
  apply lratCheckerSound f10545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10545
  · intro a ha; simp [p10545] at ha; subst a; trivial
  · exact checked10545
theorem derived10545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10545 := by
  apply localUnsat_implies_entails f10545 [c9748, c1594] c10545 unsat10545 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1594 := h 1593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10546 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1608, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p10546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10546 : lratChecker f10546 p10546 = .success := by decide +kernel
theorem unsat10546 : Unsatisfiable (PosFin 65) f10546 := by
  apply lratCheckerSound f10546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10546
  · intro a ha; simp [p10546] at ha; subst a; trivial
  · exact checked10546
theorem derived10546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10546 := by
  apply localUnsat_implies_entails f10546 [c9748, c1608] c10546 unsat10546 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1608 := h 1607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10547 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1609, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p10547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10547 : lratChecker f10547 p10547 = .success := by decide +kernel
theorem unsat10547 : Unsatisfiable (PosFin 65) f10547 := by
  apply lratCheckerSound f10547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10547
  · intro a ha; simp [p10547] at ha; subst a; trivial
  · exact checked10547
theorem derived10547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10547 := by
  apply localUnsat_implies_entails f10547 [c9748, c1609] c10547 unsat10547 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1609 := h 1608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10548 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c2271, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p10548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10548 : lratChecker f10548 p10548 = .success := by decide +kernel
theorem unsat10548 : Unsatisfiable (PosFin 65) f10548 := by
  apply lratCheckerSound f10548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10548
  · intro a ha; simp [p10548] at ha; subst a; trivial
  · exact checked10548
theorem derived10548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10548 := by
  apply localUnsat_implies_entails f10548 [c9748, c2271] c10548 unsat10548 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c2271 := h 2270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10549 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1599, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10549 : lratChecker f10549 p10549 = .success := by decide +kernel
theorem unsat10549 : Unsatisfiable (PosFin 65) f10549 := by
  apply lratCheckerSound f10549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10549
  · intro a ha; simp [p10549] at ha; subst a; trivial
  · exact checked10549
theorem derived10549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10549 := by
  apply localUnsat_implies_entails f10549 [c9748, c1599] c10549 unsat10549 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1599 := h 1598 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10550 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c1603, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p10550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked10550 : lratChecker f10550 p10550 = .success := by decide +kernel
theorem unsat10550 : Unsatisfiable (PosFin 65) f10550 := by
  apply lratCheckerSound f10550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10550
  · intro a ha; simp [p10550] at ha; subst a; trivial
  · exact checked10550
theorem derived10550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c10550 := by
  apply localUnsat_implies_entails f10550 [c9748, c1603] c10550 unsat10550 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c1603 := h 1602 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived10550

end CochromaticTwenty.Certificates.FixedCore0
