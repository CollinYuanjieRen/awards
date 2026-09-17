import MerLeanExperiment.Certificates.FixedCore1.Steps2500_2599

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8481 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c661, some c650, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8481 : lratChecker f8481 p8481 = .success := by decide +kernel
theorem unsat8481 : Unsatisfiable (PosFin 65) f8481 := by
  apply lratCheckerSound f8481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8481
  · intro a ha; simp [p8481] at ha; subst a; trivial
  · exact checked8481
theorem derived8481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8481 := by
  apply localUnsat_implies_entails f8481 [c661, c650] c8481 unsat8481 (by rfl) a
  have h0 : Entails.eval a c661 := h 660 (by decide)
  have h1 : Entails.eval a c650 := h 649 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8482 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2483, some c2493, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8482 : lratChecker f8482 p8482 = .success := by decide +kernel
theorem unsat8482 : Unsatisfiable (PosFin 65) f8482 := by
  apply lratCheckerSound f8482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8482
  · intro a ha; simp [p8482] at ha; subst a; trivial
  · exact checked8482
theorem derived8482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8482 := by
  apply localUnsat_implies_entails f8482 [c2483, c2493] c8482 unsat8482 (by rfl) a
  have h0 : Entails.eval a c2483 := h 2482 (by decide)
  have h1 : Entails.eval a c2493 := h 2492 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8483 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1833, some c1789, some c1633, some c1538, some c909, some c1101, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8483 : lratChecker f8483 p8483 = .success := by decide +kernel
theorem unsat8483 : Unsatisfiable (PosFin 65) f8483 := by
  apply lratCheckerSound f8483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8483
  · intro a ha; simp [p8483] at ha; subst a; trivial
  · exact checked8483
theorem derived8483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8483 := by
  apply localUnsat_implies_entails f8483 [c1833, c1789, c1633, c1538, c909, c1101] c8483 unsat8483 (by rfl) a
  have h0 : Entails.eval a c1833 := h 1832 (by decide)
  have h1 : Entails.eval a c1789 := h 1788 (by decide)
  have h2 : Entails.eval a c1633 := h 1632 (by decide)
  have h3 : Entails.eval a c1538 := h 1537 (by decide)
  have h4 : Entails.eval a c909 := h 908 (by decide)
  have h5 : Entails.eval a c1101 := h 1100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8484 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8378, some c8098, some c454, some c434, some c439, some c426, some c8382, some c8394, some c421, some c8480, some c449, some c429, some c8482, some c483, some c8483, some c1845, some c1800, some c1642, some c1547, some c1038, some c920, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8484 : lratChecker f8484 p8484 = .success := by decide +kernel
theorem unsat8484 : Unsatisfiable (PosFin 65) f8484 := by
  apply lratCheckerSound f8484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8484
  · intro a ha; simp [p8484] at ha; subst a; trivial
  · exact checked8484
theorem derived8484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8484 := by
  apply localUnsat_implies_entails f8484 [c8378, c8098, c454, c434, c439, c426, c8382, c8394, c421, c8480, c449, c429, c8482, c483, c8483, c1845, c1800, c1642, c1547, c1038, c920] c8484 unsat8484 (by rfl) a
  have h0 : Entails.eval a c8378 := derived8378 a h
  have h1 : Entails.eval a c8098 := derived8098 a h
  have h2 : Entails.eval a c454 := h 453 (by decide)
  have h3 : Entails.eval a c434 := h 433 (by decide)
  have h4 : Entails.eval a c439 := h 438 (by decide)
  have h5 : Entails.eval a c426 := h 425 (by decide)
  have h6 : Entails.eval a c8382 := derived8382 a h
  have h7 : Entails.eval a c8394 := derived8394 a h
  have h8 : Entails.eval a c421 := h 420 (by decide)
  have h9 : Entails.eval a c8480 := derived8480 a h
  have h10 : Entails.eval a c449 := h 448 (by decide)
  have h11 : Entails.eval a c429 := h 428 (by decide)
  have h12 : Entails.eval a c8482 := derived8482 a h
  have h13 : Entails.eval a c483 := h 482 (by decide)
  have h14 : Entails.eval a c8483 := derived8483 a h
  have h15 : Entails.eval a c1845 := h 1844 (by decide)
  have h16 : Entails.eval a c1800 := h 1799 (by decide)
  have h17 : Entails.eval a c1642 := h 1641 (by decide)
  have h18 : Entails.eval a c1547 := h 1546 (by decide)
  have h19 : Entails.eval a c1038 := h 1037 (by decide)
  have h20 : Entails.eval a c920 := h 919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8485 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2567, some c569, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8485 : lratChecker f8485 p8485 = .success := by decide +kernel
theorem unsat8485 : Unsatisfiable (PosFin 65) f8485 := by
  apply lratCheckerSound f8485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8485
  · intro a ha; simp [p8485] at ha; subst a; trivial
  · exact checked8485
theorem derived8485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8485 := by
  apply localUnsat_implies_entails f8485 [c2567, c569] c8485 unsat8485 (by rfl) a
  have h0 : Entails.eval a c2567 := h 2566 (by decide)
  have h1 : Entails.eval a c569 := h 568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8486 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2610, some c1508, some c1307, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8486 : lratChecker f8486 p8486 = .success := by decide +kernel
theorem unsat8486 : Unsatisfiable (PosFin 65) f8486 := by
  apply lratCheckerSound f8486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8486
  · intro a ha; simp [p8486] at ha; subst a; trivial
  · exact checked8486
theorem derived8486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8486 := by
  apply localUnsat_implies_entails f8486 [c2610, c1508, c1307] c8486 unsat8486 (by rfl) a
  have h0 : Entails.eval a c2610 := h 2609 (by decide)
  have h1 : Entails.eval a c1508 := h 1507 (by decide)
  have h2 : Entails.eval a c1307 := h 1306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8487 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8484, some c8378, some c8420, some c7976, some c8486, some c1497, some c8117, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8487 : lratChecker f8487 p8487 = .success := by decide +kernel
theorem unsat8487 : Unsatisfiable (PosFin 65) f8487 := by
  apply lratCheckerSound f8487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8487
  · intro a ha; simp [p8487] at ha; subst a; trivial
  · exact checked8487
theorem derived8487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8487 := by
  apply localUnsat_implies_entails f8487 [c8484, c8378, c8420, c7976, c8486, c1497, c8117] c8487 unsat8487 (by rfl) a
  have h0 : Entails.eval a c8484 := derived8484 a h
  have h1 : Entails.eval a c8378 := derived8378 a h
  have h2 : Entails.eval a c8420 := derived8420 a h
  have h3 : Entails.eval a c7976 := derived7976 a h
  have h4 : Entails.eval a c8486 := derived8486 a h
  have h5 : Entails.eval a c1497 := h 1496 (by decide)
  have h6 : Entails.eval a c8117 := derived8117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8488 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8484, some c8378, some c8487, some c8416, some c8341, some c7976, some c1572, some c1836, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8488 : lratChecker f8488 p8488 = .success := by decide +kernel
theorem unsat8488 : Unsatisfiable (PosFin 65) f8488 := by
  apply lratCheckerSound f8488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8488
  · intro a ha; simp [p8488] at ha; subst a; trivial
  · exact checked8488
theorem derived8488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8488 := by
  apply localUnsat_implies_entails f8488 [c8484, c8378, c8487, c8416, c8341, c7976, c1572, c1836] c8488 unsat8488 (by rfl) a
  have h0 : Entails.eval a c8484 := derived8484 a h
  have h1 : Entails.eval a c8378 := derived8378 a h
  have h2 : Entails.eval a c8487 := derived8487 a h
  have h3 : Entails.eval a c8416 := derived8416 a h
  have h4 : Entails.eval a c8341 := derived8341 a h
  have h5 : Entails.eval a c7976 := derived7976 a h
  have h6 : Entails.eval a c1572 := h 1571 (by decide)
  have h7 : Entails.eval a c1836 := h 1835 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8489 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c480, some c8414, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8489 : lratChecker f8489 p8489 = .success := by decide +kernel
theorem unsat8489 : Unsatisfiable (PosFin 65) f8489 := by
  apply lratCheckerSound f8489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8489
  · intro a ha; simp [p8489] at ha; subst a; trivial
  · exact checked8489
theorem derived8489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8489 := by
  apply localUnsat_implies_entails f8489 [c480, c8414] c8489 unsat8489 (by rfl) a
  have h0 : Entails.eval a c480 := h 479 (by decide)
  have h1 : Entails.eval a c8414 := derived8414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8490 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2557, some c2572, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8490 : lratChecker f8490 p8490 = .success := by decide +kernel
theorem unsat8490 : Unsatisfiable (PosFin 65) f8490 := by
  apply lratCheckerSound f8490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8490
  · intro a ha; simp [p8490] at ha; subst a; trivial
  · exact checked8490
theorem derived8490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8490 := by
  apply localUnsat_implies_entails f8490 [c2557, c2572] c8490 unsat8490 (by rfl) a
  have h0 : Entails.eval a c2557 := h 2556 (by decide)
  have h1 : Entails.eval a c2572 := h 2571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8491 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c573, some c571, some c574, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8491 : lratChecker f8491 p8491 = .success := by decide +kernel
theorem unsat8491 : Unsatisfiable (PosFin 65) f8491 := by
  apply lratCheckerSound f8491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8491
  · intro a ha; simp [p8491] at ha; subst a; trivial
  · exact checked8491
theorem derived8491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8491 := by
  apply localUnsat_implies_entails f8491 [c573, c571, c574] c8491 unsat8491 (by rfl) a
  have h0 : Entails.eval a c573 := h 572 (by decide)
  have h1 : Entails.eval a c571 := h 570 (by decide)
  have h2 : Entails.eval a c574 := h 573 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8492 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8485, some c8491, some c2572, some c2559, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8492 : lratChecker f8492 p8492 = .success := by decide +kernel
theorem unsat8492 : Unsatisfiable (PosFin 65) f8492 := by
  apply lratCheckerSound f8492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8492
  · intro a ha; simp [p8492] at ha; subst a; trivial
  · exact checked8492
theorem derived8492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8492 := by
  apply localUnsat_implies_entails f8492 [c8485, c8491, c2572, c2559] c8492 unsat8492 (by rfl) a
  have h0 : Entails.eval a c8485 := derived8485 a h
  have h1 : Entails.eval a c8491 := derived8491 a h
  have h2 : Entails.eval a c2572 := h 2571 (by decide)
  have h3 : Entails.eval a c2559 := h 2558 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8493 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8378, some c8420, some c7976, some c8489, some c8492, some c2435, some c2443, some c2427, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8493 : lratChecker f8493 p8493 = .success := by decide +kernel
theorem unsat8493 : Unsatisfiable (PosFin 65) f8493 := by
  apply lratCheckerSound f8493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8493
  · intro a ha; simp [p8493] at ha; subst a; trivial
  · exact checked8493
theorem derived8493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8493 := by
  apply localUnsat_implies_entails f8493 [c8378, c8420, c7976, c8489, c8492, c2435, c2443, c2427] c8493 unsat8493 (by rfl) a
  have h0 : Entails.eval a c8378 := derived8378 a h
  have h1 : Entails.eval a c8420 := derived8420 a h
  have h2 : Entails.eval a c7976 := derived7976 a h
  have h3 : Entails.eval a c8489 := derived8489 a h
  have h4 : Entails.eval a c8492 := derived8492 a h
  have h5 : Entails.eval a c2435 := h 2434 (by decide)
  have h6 : Entails.eval a c2443 := h 2442 (by decide)
  have h7 : Entails.eval a c2427 := h 2426 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8494 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8378, some c8484, some c8488, some c8493, some c8416, some c8341, some c7976, some c8418, some c8490, some c1744, some c1742, some c1747, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8494 : lratChecker f8494 p8494 = .success := by decide +kernel
theorem unsat8494 : Unsatisfiable (PosFin 65) f8494 := by
  apply lratCheckerSound f8494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8494
  · intro a ha; simp [p8494] at ha; subst a; trivial
  · exact checked8494
theorem derived8494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8494 := by
  apply localUnsat_implies_entails f8494 [c8378, c8484, c8488, c8493, c8416, c8341, c7976, c8418, c8490, c1744, c1742, c1747] c8494 unsat8494 (by rfl) a
  have h0 : Entails.eval a c8378 := derived8378 a h
  have h1 : Entails.eval a c8484 := derived8484 a h
  have h2 : Entails.eval a c8488 := derived8488 a h
  have h3 : Entails.eval a c8493 := derived8493 a h
  have h4 : Entails.eval a c8416 := derived8416 a h
  have h5 : Entails.eval a c8341 := derived8341 a h
  have h6 : Entails.eval a c7976 := derived7976 a h
  have h7 : Entails.eval a c8418 := derived8418 a h
  have h8 : Entails.eval a c8490 := derived8490 a h
  have h9 : Entails.eval a c1744 := h 1743 (by decide)
  have h10 : Entails.eval a c1742 := h 1741 (by decide)
  have h11 : Entails.eval a c1747 := h 1746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8495 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨10, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1833, some c1789, some c1633, some c1538, some c917, some c1101, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8495 : lratChecker f8495 p8495 = .success := by decide +kernel
theorem unsat8495 : Unsatisfiable (PosFin 65) f8495 := by
  apply lratCheckerSound f8495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8495
  · intro a ha; simp [p8495] at ha; subst a; trivial
  · exact checked8495
theorem derived8495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8495 := by
  apply localUnsat_implies_entails f8495 [c1833, c1789, c1633, c1538, c917, c1101] c8495 unsat8495 (by rfl) a
  have h0 : Entails.eval a c1833 := h 1832 (by decide)
  have h1 : Entails.eval a c1789 := h 1788 (by decide)
  have h2 : Entails.eval a c1633 := h 1632 (by decide)
  have h3 : Entails.eval a c1538 := h 1537 (by decide)
  have h4 : Entails.eval a c917 := h 916 (by decide)
  have h5 : Entails.eval a c1101 := h 1100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8496 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8494, some c8378, some c8098, some c8402, some c2012, some c7976, some c2144, some c2176, some c1991, some c8177, some c2011, some c2150, some c2169, some c8394, some c8495, some c1845, some c1800, some c1642, some c1547, some c1038, some c920, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8496 : lratChecker f8496 p8496 = .success := by decide +kernel
theorem unsat8496 : Unsatisfiable (PosFin 65) f8496 := by
  apply lratCheckerSound f8496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8496
  · intro a ha; simp [p8496] at ha; subst a; trivial
  · exact checked8496
theorem derived8496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8496 := by
  apply localUnsat_implies_entails f8496 [c8494, c8378, c8098, c8402, c2012, c7976, c2144, c2176, c1991, c8177, c2011, c2150, c2169, c8394, c8495, c1845, c1800, c1642, c1547, c1038, c920] c8496 unsat8496 (by rfl) a
  have h0 : Entails.eval a c8494 := derived8494 a h
  have h1 : Entails.eval a c8378 := derived8378 a h
  have h2 : Entails.eval a c8098 := derived8098 a h
  have h3 : Entails.eval a c8402 := derived8402 a h
  have h4 : Entails.eval a c2012 := h 2011 (by decide)
  have h5 : Entails.eval a c7976 := derived7976 a h
  have h6 : Entails.eval a c2144 := h 2143 (by decide)
  have h7 : Entails.eval a c2176 := h 2175 (by decide)
  have h8 : Entails.eval a c1991 := h 1990 (by decide)
  have h9 : Entails.eval a c8177 := derived8177 a h
  have h10 : Entails.eval a c2011 := h 2010 (by decide)
  have h11 : Entails.eval a c2150 := h 2149 (by decide)
  have h12 : Entails.eval a c2169 := h 2168 (by decide)
  have h13 : Entails.eval a c8394 := derived8394 a h
  have h14 : Entails.eval a c8495 := derived8495 a h
  have h15 : Entails.eval a c1845 := h 1844 (by decide)
  have h16 : Entails.eval a c1800 := h 1799 (by decide)
  have h17 : Entails.eval a c1642 := h 1641 (by decide)
  have h18 : Entails.eval a c1547 := h 1546 (by decide)
  have h19 : Entails.eval a c1038 := h 1037 (by decide)
  have h20 : Entails.eval a c920 := h 919 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8497 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c515, some c8391, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8497 : lratChecker f8497 p8497 = .success := by decide +kernel
theorem unsat8497 : Unsatisfiable (PosFin 65) f8497 := by
  apply lratCheckerSound f8497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8497
  · intro a ha; simp [p8497] at ha; subst a; trivial
  · exact checked8497
theorem derived8497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8497 := by
  apply localUnsat_implies_entails f8497 [c515, c8391] c8497 unsat8497 (by rfl) a
  have h0 : Entails.eval a c515 := h 514 (by decide)
  have h1 : Entails.eval a c8391 := derived8391 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8498 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2143, some c2145, some c8155, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8498 : lratChecker f8498 p8498 = .success := by decide +kernel
theorem unsat8498 : Unsatisfiable (PosFin 65) f8498 := by
  apply lratCheckerSound f8498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8498
  · intro a ha; simp [p8498] at ha; subst a; trivial
  · exact checked8498
theorem derived8498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8498 := by
  apply localUnsat_implies_entails f8498 [c2143, c2145, c8155] c8498 unsat8498 (by rfl) a
  have h0 : Entails.eval a c2143 := h 2142 (by decide)
  have h1 : Entails.eval a c2145 := h 2144 (by decide)
  have h2 : Entails.eval a c8155 := derived8155 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8499 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8496, some c8494, some c8378, some c8497, some c8498, some c2179, some c2161, some c2160, some c2153, some c8155, some c8492, some c8394, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8499 : lratChecker f8499 p8499 = .success := by decide +kernel
theorem unsat8499 : Unsatisfiable (PosFin 65) f8499 := by
  apply lratCheckerSound f8499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8499
  · intro a ha; simp [p8499] at ha; subst a; trivial
  · exact checked8499
theorem derived8499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8499 := by
  apply localUnsat_implies_entails f8499 [c8496, c8494, c8378, c8497, c8498, c2179, c2161, c2160, c2153, c8155, c8492, c8394] c8499 unsat8499 (by rfl) a
  have h0 : Entails.eval a c8496 := derived8496 a h
  have h1 : Entails.eval a c8494 := derived8494 a h
  have h2 : Entails.eval a c8378 := derived8378 a h
  have h3 : Entails.eval a c8497 := derived8497 a h
  have h4 : Entails.eval a c8498 := derived8498 a h
  have h5 : Entails.eval a c2179 := h 2178 (by decide)
  have h6 : Entails.eval a c2161 := h 2160 (by decide)
  have h7 : Entails.eval a c2160 := h 2159 (by decide)
  have h8 : Entails.eval a c2153 := h 2152 (by decide)
  have h9 : Entails.eval a c8155 := derived8155 a h
  have h10 : Entails.eval a c8492 := derived8492 a h
  have h11 : Entails.eval a c8394 := derived8394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8500 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8378, some c8494, some c8496, some c8499, some c8341, some c8426, some c8490, some c8418, some c1734, some c1747, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8500 : lratChecker f8500 p8500 = .success := by decide +kernel
theorem unsat8500 : Unsatisfiable (PosFin 65) f8500 := by
  apply lratCheckerSound f8500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8500
  · intro a ha; simp [p8500] at ha; subst a; trivial
  · exact checked8500
theorem derived8500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8500 := by
  apply localUnsat_implies_entails f8500 [c8378, c8494, c8496, c8499, c8341, c8426, c8490, c8418, c1734, c1747] c8500 unsat8500 (by rfl) a
  have h0 : Entails.eval a c8378 := derived8378 a h
  have h1 : Entails.eval a c8494 := derived8494 a h
  have h2 : Entails.eval a c8496 := derived8496 a h
  have h3 : Entails.eval a c8499 := derived8499 a h
  have h4 : Entails.eval a c8341 := derived8341 a h
  have h5 : Entails.eval a c8426 := derived8426 a h
  have h6 : Entails.eval a c8490 := derived8490 a h
  have h7 : Entails.eval a c8418 := derived8418 a h
  have h8 : Entails.eval a c1734 := h 1733 (by decide)
  have h9 : Entails.eval a c1747 := h 1746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8501 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c852, some c843, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8501 : lratChecker f8501 p8501 = .success := by decide +kernel
theorem unsat8501 : Unsatisfiable (PosFin 65) f8501 := by
  apply lratCheckerSound f8501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8501
  · intro a ha; simp [p8501] at ha; subst a; trivial
  · exact checked8501
theorem derived8501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8501 := by
  apply localUnsat_implies_entails f8501 [c852, c843] c8501 unsat8501 (by rfl) a
  have h0 : Entails.eval a c852 := h 851 (by decide)
  have h1 : Entails.eval a c843 := h 842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8502 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c424, some c436, some c446, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8502 : lratChecker f8502 p8502 = .success := by decide +kernel
theorem unsat8502 : Unsatisfiable (PosFin 65) f8502 := by
  apply lratCheckerSound f8502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8502
  · intro a ha; simp [p8502] at ha; subst a; trivial
  · exact checked8502
theorem derived8502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8502 := by
  apply localUnsat_implies_entails f8502 [c424, c436, c446] c8502 unsat8502 (by rfl) a
  have h0 : Entails.eval a c424 := h 423 (by decide)
  have h1 : Entails.eval a c436 := h 435 (by decide)
  have h2 : Entails.eval a c446 := h 445 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8503 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2648, some c819, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8503 : lratChecker f8503 p8503 = .success := by decide +kernel
theorem unsat8503 : Unsatisfiable (PosFin 65) f8503 := by
  apply lratCheckerSound f8503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8503
  · intro a ha; simp [p8503] at ha; subst a; trivial
  · exact checked8503
theorem derived8503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8503 := by
  apply localUnsat_implies_entails f8503 [c2648, c819] c8503 unsat8503 (by rfl) a
  have h0 : Entails.eval a c2648 := h 2647 (by decide)
  have h1 : Entails.eval a c819 := h 818 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8504 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨9, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6708, some c6709, some c2138, some c70, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8504 : lratChecker f8504 p8504 = .success := by decide +kernel
theorem unsat8504 : Unsatisfiable (PosFin 65) f8504 := by
  apply lratCheckerSound f8504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8504
  · intro a ha; simp [p8504] at ha; subst a; trivial
  · exact checked8504
theorem derived8504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8504 := by
  apply localUnsat_implies_entails f8504 [c6708, c6709, c2138, c70] c8504 unsat8504 (by rfl) a
  have h0 : Entails.eval a c6708 := derived6708 a h
  have h1 : Entails.eval a c6709 := derived6709 a h
  have h2 : Entails.eval a c2138 := h 2137 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8505 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c434, some c8502, some c449, some c429, some c475, some c8481, some c8503, some c454, some c8501, some c8098, some c1833, some c1789, some c2234, some c1538, some c1456, some c8504, some c166, some c420, some c67, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8505 : lratChecker f8505 p8505 = .success := by decide +kernel
theorem unsat8505 : Unsatisfiable (PosFin 65) f8505 := by
  apply lratCheckerSound f8505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8505
  · intro a ha; simp [p8505] at ha; subst a; trivial
  · exact checked8505
theorem derived8505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8505 := by
  apply localUnsat_implies_entails f8505 [c434, c8502, c449, c429, c475, c8481, c8503, c454, c8501, c8098, c1833, c1789, c2234, c1538, c1456, c8504, c166, c420, c67] c8505 unsat8505 (by rfl) a
  have h0 : Entails.eval a c434 := h 433 (by decide)
  have h1 : Entails.eval a c8502 := derived8502 a h
  have h2 : Entails.eval a c449 := h 448 (by decide)
  have h3 : Entails.eval a c429 := h 428 (by decide)
  have h4 : Entails.eval a c475 := h 474 (by decide)
  have h5 : Entails.eval a c8481 := derived8481 a h
  have h6 : Entails.eval a c8503 := derived8503 a h
  have h7 : Entails.eval a c454 := h 453 (by decide)
  have h8 : Entails.eval a c8501 := derived8501 a h
  have h9 : Entails.eval a c8098 := derived8098 a h
  have h10 : Entails.eval a c1833 := h 1832 (by decide)
  have h11 : Entails.eval a c1789 := h 1788 (by decide)
  have h12 : Entails.eval a c2234 := h 2233 (by decide)
  have h13 : Entails.eval a c1538 := h 1537 (by decide)
  have h14 : Entails.eval a c1456 := h 1455 (by decide)
  have h15 : Entails.eval a c8504 := derived8504 a h
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c420 := h 419 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8506 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8098, some c454, some c434, some c439, some c426, some c8501, some c8394, some c8502, some c449, some c8482, some c483, some c8503, some c429, some c475, some c8481, some c8505, some c2235, some c1845, some c1800, some c1773, some c1038, some c8504, some c966, some c420, some c3288, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked8506 : lratChecker f8506 p8506 = .success := by decide +kernel
theorem unsat8506 : Unsatisfiable (PosFin 65) f8506 := by
  apply lratCheckerSound f8506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8506
  · intro a ha; simp [p8506] at ha; subst a; trivial
  · exact checked8506
theorem derived8506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8506 := by
  apply localUnsat_implies_entails f8506 [c8500, c8098, c454, c434, c439, c426, c8501, c8394, c8502, c449, c8482, c483, c8503, c429, c475, c8481, c8505, c2235, c1845, c1800, c1773, c1038, c8504, c966, c420, c3288] c8506 unsat8506 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8098 := derived8098 a h
  have h2 : Entails.eval a c454 := h 453 (by decide)
  have h3 : Entails.eval a c434 := h 433 (by decide)
  have h4 : Entails.eval a c439 := h 438 (by decide)
  have h5 : Entails.eval a c426 := h 425 (by decide)
  have h6 : Entails.eval a c8501 := derived8501 a h
  have h7 : Entails.eval a c8394 := derived8394 a h
  have h8 : Entails.eval a c8502 := derived8502 a h
  have h9 : Entails.eval a c449 := h 448 (by decide)
  have h10 : Entails.eval a c8482 := derived8482 a h
  have h11 : Entails.eval a c483 := h 482 (by decide)
  have h12 : Entails.eval a c8503 := derived8503 a h
  have h13 : Entails.eval a c429 := h 428 (by decide)
  have h14 : Entails.eval a c475 := h 474 (by decide)
  have h15 : Entails.eval a c8481 := derived8481 a h
  have h16 : Entails.eval a c8505 := derived8505 a h
  have h17 : Entails.eval a c2235 := h 2234 (by decide)
  have h18 : Entails.eval a c1845 := h 1844 (by decide)
  have h19 : Entails.eval a c1800 := h 1799 (by decide)
  have h20 : Entails.eval a c1773 := h 1772 (by decide)
  have h21 : Entails.eval a c1038 := h 1037 (by decide)
  have h22 : Entails.eval a c8504 := derived8504 a h
  have h23 : Entails.eval a c966 := h 965 (by decide)
  have h24 : Entails.eval a c420 := h 419 (by decide)
  have h25 : Entails.eval a c3288 := h 3287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8507 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2338, some c2345, some c2316, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8507 : lratChecker f8507 p8507 = .success := by decide +kernel
theorem unsat8507 : Unsatisfiable (PosFin 65) f8507 := by
  apply lratCheckerSound f8507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8507
  · intro a ha; simp [p8507] at ha; subst a; trivial
  · exact checked8507
theorem derived8507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8507 := by
  apply localUnsat_implies_entails f8507 [c2338, c2345, c2316] c8507 unsat8507 (by rfl) a
  have h0 : Entails.eval a c2338 := h 2337 (by decide)
  have h1 : Entails.eval a c2345 := h 2344 (by decide)
  have h2 : Entails.eval a c2316 := h 2315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8508 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2265, some c679, some c693, some c690, some c681, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8508 : lratChecker f8508 p8508 = .success := by decide +kernel
theorem unsat8508 : Unsatisfiable (PosFin 65) f8508 := by
  apply lratCheckerSound f8508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8508
  · intro a ha; simp [p8508] at ha; subst a; trivial
  · exact checked8508
theorem derived8508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8508 := by
  apply localUnsat_implies_entails f8508 [c2265, c679, c693, c690, c681] c8508 unsat8508 (by rfl) a
  have h0 : Entails.eval a c2265 := h 2264 (by decide)
  have h1 : Entails.eval a c679 := h 678 (by decide)
  have h2 : Entails.eval a c693 := h 692 (by decide)
  have h3 : Entails.eval a c690 := h 689 (by decide)
  have h4 : Entails.eval a c681 := h 680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8509 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8451, some c2243, some c670, some c690, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8509 : lratChecker f8509 p8509 = .success := by decide +kernel
theorem unsat8509 : Unsatisfiable (PosFin 65) f8509 := by
  apply lratCheckerSound f8509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8509
  · intro a ha; simp [p8509] at ha; subst a; trivial
  · exact checked8509
theorem derived8509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8509 := by
  apply localUnsat_implies_entails f8509 [c8451, c2243, c670, c690] c8509 unsat8509 (by rfl) a
  have h0 : Entails.eval a c8451 := derived8451 a h
  have h1 : Entails.eval a c2243 := h 2242 (by decide)
  have h2 : Entails.eval a c670 := h 669 (by decide)
  have h3 : Entails.eval a c690 := h 689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8510 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8508, some c8509, some c680, some c2258, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8510 : lratChecker f8510 p8510 = .success := by decide +kernel
theorem unsat8510 : Unsatisfiable (PosFin 65) f8510 := by
  apply lratCheckerSound f8510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8510
  · intro a ha; simp [p8510] at ha; subst a; trivial
  · exact checked8510
theorem derived8510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8510 := by
  apply localUnsat_implies_entails f8510 [c8500, c8508, c8509, c680, c2258] c8510 unsat8510 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8508 := derived8508 a h
  have h2 : Entails.eval a c8509 := derived8509 a h
  have h3 : Entails.eval a c680 := h 679 (by decide)
  have h4 : Entails.eval a c2258 := h 2257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8511 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2386, some c2092, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8511 : lratChecker f8511 p8511 = .success := by decide +kernel
theorem unsat8511 : Unsatisfiable (PosFin 65) f8511 := by
  apply lratCheckerSound f8511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8511
  · intro a ha; simp [p8511] at ha; subst a; trivial
  · exact checked8511
theorem derived8511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8511 := by
  apply localUnsat_implies_entails f8511 [c2386, c2092] c8511 unsat8511 (by rfl) a
  have h0 : Entails.eval a c2386 := h 2385 (by decide)
  have h1 : Entails.eval a c2092 := h 2091 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8512 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8507, some c8511, some c8510, some c8416, some c1572, some c1836, some c1257, some c8503, some c1374, some c2394, some c2483, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8512 : lratChecker f8512 p8512 = .success := by decide +kernel
theorem unsat8512 : Unsatisfiable (PosFin 65) f8512 := by
  apply lratCheckerSound f8512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8512
  · intro a ha; simp [p8512] at ha; subst a; trivial
  · exact checked8512
theorem derived8512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8512 := by
  apply localUnsat_implies_entails f8512 [c8500, c8507, c8511, c8510, c8416, c1572, c1836, c1257, c8503, c1374, c2394, c2483] c8512 unsat8512 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8507 := derived8507 a h
  have h2 : Entails.eval a c8511 := derived8511 a h
  have h3 : Entails.eval a c8510 := derived8510 a h
  have h4 : Entails.eval a c8416 := derived8416 a h
  have h5 : Entails.eval a c1572 := h 1571 (by decide)
  have h6 : Entails.eval a c1836 := h 1835 (by decide)
  have h7 : Entails.eval a c1257 := h 1256 (by decide)
  have h8 : Entails.eval a c8503 := derived8503 a h
  have h9 : Entails.eval a c1374 := h 1373 (by decide)
  have h10 : Entails.eval a c2394 := h 2393 (by decide)
  have h11 : Entails.eval a c2483 := h 2482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8513 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8503, some c8463, some c2394, some c2483, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8513 : lratChecker f8513 p8513 = .success := by decide +kernel
theorem unsat8513 : Unsatisfiable (PosFin 65) f8513 := by
  apply lratCheckerSound f8513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8513
  · intro a ha; simp [p8513] at ha; subst a; trivial
  · exact checked8513
theorem derived8513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8513 := by
  apply localUnsat_implies_entails f8513 [c8503, c8463, c2394, c2483] c8513 unsat8513 (by rfl) a
  have h0 : Entails.eval a c8503 := derived8503 a h
  have h1 : Entails.eval a c8463 := derived8463 a h
  have h2 : Entails.eval a c2394 := h 2393 (by decide)
  have h3 : Entails.eval a c2483 := h 2482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8514 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8507, some c8511, some c8510, some c8416, some c8512, some c8513, some c8418, some c8490, some c1742, some c1747, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8514 : lratChecker f8514 p8514 = .success := by decide +kernel
theorem unsat8514 : Unsatisfiable (PosFin 65) f8514 := by
  apply lratCheckerSound f8514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8514
  · intro a ha; simp [p8514] at ha; subst a; trivial
  · exact checked8514
theorem derived8514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8514 := by
  apply localUnsat_implies_entails f8514 [c8500, c8507, c8511, c8510, c8416, c8512, c8513, c8418, c8490, c1742, c1747] c8514 unsat8514 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8507 := derived8507 a h
  have h2 : Entails.eval a c8511 := derived8511 a h
  have h3 : Entails.eval a c8510 := derived8510 a h
  have h4 : Entails.eval a c8416 := derived8416 a h
  have h5 : Entails.eval a c8512 := derived8512 a h
  have h6 : Entails.eval a c8513 := derived8513 a h
  have h7 : Entails.eval a c8418 := derived8418 a h
  have h8 : Entails.eval a c8490 := derived8490 a h
  have h9 : Entails.eval a c1742 := h 1741 (by decide)
  have h10 : Entails.eval a c1747 := h 1746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8515 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8500, some c8506, some c8507, some c8510, some c8416, some c8511, some c8514, some c1608, some c2265, some c1828, some c581, some c8503, some c2394, some c2483, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8515 : lratChecker f8515 p8515 = .success := by decide +kernel
theorem unsat8515 : Unsatisfiable (PosFin 65) f8515 := by
  apply lratCheckerSound f8515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8515
  · intro a ha; simp [p8515] at ha; subst a; trivial
  · exact checked8515
theorem derived8515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8515 := by
  apply localUnsat_implies_entails f8515 [c8500, c8506, c8507, c8510, c8416, c8511, c8514, c1608, c2265, c1828, c581, c8503, c2394, c2483] c8515 unsat8515 (by rfl) a
  have h0 : Entails.eval a c8500 := derived8500 a h
  have h1 : Entails.eval a c8506 := derived8506 a h
  have h2 : Entails.eval a c8507 := derived8507 a h
  have h3 : Entails.eval a c8510 := derived8510 a h
  have h4 : Entails.eval a c8416 := derived8416 a h
  have h5 : Entails.eval a c8511 := derived8511 a h
  have h6 : Entails.eval a c8514 := derived8514 a h
  have h7 : Entails.eval a c1608 := h 1607 (by decide)
  have h8 : Entails.eval a c2265 := h 2264 (by decide)
  have h9 : Entails.eval a c1828 := h 1827 (by decide)
  have h10 : Entails.eval a c581 := h 580 (by decide)
  have h11 : Entails.eval a c8503 := derived8503 a h
  have h12 : Entails.eval a c2394 := h 2393 (by decide)
  have h13 : Entails.eval a c2483 := h 2482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8516 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2017, some c2016, some c2926, some c1959, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8516 : lratChecker f8516 p8516 = .success := by decide +kernel
theorem unsat8516 : Unsatisfiable (PosFin 65) f8516 := by
  apply lratCheckerSound f8516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8516
  · intro a ha; simp [p8516] at ha; subst a; trivial
  · exact checked8516
theorem derived8516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8516 := by
  apply localUnsat_implies_entails f8516 [c2017, c2016, c2926, c1959] c8516 unsat8516 (by rfl) a
  have h0 : Entails.eval a c2017 := h 2016 (by decide)
  have h1 : Entails.eval a c2016 := h 2015 (by decide)
  have h2 : Entails.eval a c2926 := h 2925 (by decide)
  have h3 : Entails.eval a c1959 := h 1958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8517 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨30, by decide⟩, true), (⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2144, some c1833, some c1803, some c8516, some c166, some c164, some c67, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8517 : lratChecker f8517 p8517 = .success := by decide +kernel
theorem unsat8517 : Unsatisfiable (PosFin 65) f8517 := by
  apply lratCheckerSound f8517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8517
  · intro a ha; simp [p8517] at ha; subst a; trivial
  · exact checked8517
theorem derived8517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8517 := by
  apply localUnsat_implies_entails f8517 [c2144, c1833, c1803, c8516, c166, c164, c67] c8517 unsat8517 (by rfl) a
  have h0 : Entails.eval a c2144 := h 2143 (by decide)
  have h1 : Entails.eval a c1833 := h 1832 (by decide)
  have h2 : Entails.eval a c1803 := h 1802 (by decide)
  have h3 : Entails.eval a c8516 := derived8516 a h
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8518 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2017, some c2016, some c2181, some c1959, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8518 : lratChecker f8518 p8518 = .success := by decide +kernel
theorem unsat8518 : Unsatisfiable (PosFin 65) f8518 := by
  apply lratCheckerSound f8518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8518
  · intro a ha; simp [p8518] at ha; subst a; trivial
  · exact checked8518
theorem derived8518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8518 := by
  apply localUnsat_implies_entails f8518 [c2017, c2016, c2181, c1959] c8518 unsat8518 (by rfl) a
  have h0 : Entails.eval a c2017 := h 2016 (by decide)
  have h1 : Entails.eval a c2016 := h 2015 (by decide)
  have h2 : Entails.eval a c2181 := h 2180 (by decide)
  have h3 : Entails.eval a c1959 := h 1958 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8519 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8479, some c8469, some c8515, some c8500, some c8098, some c1900, some c1926, some c1912, some c1923, some c1892, some c8501, some c1920, some c8482, some c8394, some c8503, some c2144, some c2176, some c8481, some c8517, some c8518, some c1887, some c82, some c3288, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked8519 : lratChecker f8519 p8519 = .success := by decide +kernel
theorem unsat8519 : Unsatisfiable (PosFin 65) f8519 := by
  apply lratCheckerSound f8519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8519
  · intro a ha; simp [p8519] at ha; subst a; trivial
  · exact checked8519
theorem derived8519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8519 := by
  apply localUnsat_implies_entails f8519 [c7849, c8377, c8479, c8469, c8515, c8500, c8098, c1900, c1926, c1912, c1923, c1892, c8501, c1920, c8482, c8394, c8503, c2144, c2176, c8481, c8517, c8518, c1887, c82, c3288] c8519 unsat8519 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8479 := derived8479 a h
  have h3 : Entails.eval a c8469 := derived8469 a h
  have h4 : Entails.eval a c8515 := derived8515 a h
  have h5 : Entails.eval a c8500 := derived8500 a h
  have h6 : Entails.eval a c8098 := derived8098 a h
  have h7 : Entails.eval a c1900 := h 1899 (by decide)
  have h8 : Entails.eval a c1926 := h 1925 (by decide)
  have h9 : Entails.eval a c1912 := h 1911 (by decide)
  have h10 : Entails.eval a c1923 := h 1922 (by decide)
  have h11 : Entails.eval a c1892 := h 1891 (by decide)
  have h12 : Entails.eval a c8501 := derived8501 a h
  have h13 : Entails.eval a c1920 := h 1919 (by decide)
  have h14 : Entails.eval a c8482 := derived8482 a h
  have h15 : Entails.eval a c8394 := derived8394 a h
  have h16 : Entails.eval a c8503 := derived8503 a h
  have h17 : Entails.eval a c2144 := h 2143 (by decide)
  have h18 : Entails.eval a c2176 := h 2175 (by decide)
  have h19 : Entails.eval a c8481 := derived8481 a h
  have h20 : Entails.eval a c8517 := derived8517 a h
  have h21 : Entails.eval a c8518 := derived8518 a h
  have h22 : Entails.eval a c1887 := h 1886 (by decide)
  have h23 : Entails.eval a c82 := h 81 (by decide)
  have h24 : Entails.eval a c3288 := h 3287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8520 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2378, some c2249, some c2528, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8520 : lratChecker f8520 p8520 = .success := by decide +kernel
theorem unsat8520 : Unsatisfiable (PosFin 65) f8520 := by
  apply lratCheckerSound f8520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8520
  · intro a ha; simp [p8520] at ha; subst a; trivial
  · exact checked8520
theorem derived8520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8520 := by
  apply localUnsat_implies_entails f8520 [c2378, c2249, c2528] c8520 unsat8520 (by rfl) a
  have h0 : Entails.eval a c2378 := h 2377 (by decide)
  have h1 : Entails.eval a c2249 := h 2248 (by decide)
  have h2 : Entails.eval a c2528 := h 2527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8521 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2106, some c2145, some c2619, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p8521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8521 : lratChecker f8521 p8521 = .success := by decide +kernel
theorem unsat8521 : Unsatisfiable (PosFin 65) f8521 := by
  apply lratCheckerSound f8521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8521
  · intro a ha; simp [p8521] at ha; subst a; trivial
  · exact checked8521
theorem derived8521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8521 := by
  apply localUnsat_implies_entails f8521 [c2106, c2145, c2619] c8521 unsat8521 (by rfl) a
  have h0 : Entails.eval a c2106 := h 2105 (by decide)
  have h1 : Entails.eval a c2145 := h 2144 (by decide)
  have h2 : Entails.eval a c2619 := h 2618 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8522 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8513, some c2386, some c2646, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8522 : lratChecker f8522 p8522 = .success := by decide +kernel
theorem unsat8522 : Unsatisfiable (PosFin 65) f8522 := by
  apply lratCheckerSound f8522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8522
  · intro a ha; simp [p8522] at ha; subst a; trivial
  · exact checked8522
theorem derived8522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8522 := by
  apply localUnsat_implies_entails f8522 [c8513, c2386, c2646] c8522 unsat8522 (by rfl) a
  have h0 : Entails.eval a c8513 := derived8513 a h
  have h1 : Entails.eval a c2386 := h 2385 (by decide)
  have h2 : Entails.eval a c2646 := h 2645 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8523 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8479, some c8377, some c7849, some c8469, some c8500, some c8515, some c8519, some c8507, some c8510, some c8336, some c8520, some c8521, some c8522, some c8418, some c8490, some c2161, some c1742, some c1747, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8523 : lratChecker f8523 p8523 = .success := by decide +kernel
theorem unsat8523 : Unsatisfiable (PosFin 65) f8523 := by
  apply lratCheckerSound f8523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8523
  · intro a ha; simp [p8523] at ha; subst a; trivial
  · exact checked8523
theorem derived8523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8523 := by
  apply localUnsat_implies_entails f8523 [c8479, c8377, c7849, c8469, c8500, c8515, c8519, c8507, c8510, c8336, c8520, c8521, c8522, c8418, c8490, c2161, c1742, c1747] c8523 unsat8523 (by rfl) a
  have h0 : Entails.eval a c8479 := derived8479 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8469 := derived8469 a h
  have h4 : Entails.eval a c8500 := derived8500 a h
  have h5 : Entails.eval a c8515 := derived8515 a h
  have h6 : Entails.eval a c8519 := derived8519 a h
  have h7 : Entails.eval a c8507 := derived8507 a h
  have h8 : Entails.eval a c8510 := derived8510 a h
  have h9 : Entails.eval a c8336 := derived8336 a h
  have h10 : Entails.eval a c8520 := derived8520 a h
  have h11 : Entails.eval a c8521 := derived8521 a h
  have h12 : Entails.eval a c8522 := derived8522 a h
  have h13 : Entails.eval a c8418 := derived8418 a h
  have h14 : Entails.eval a c8490 := derived8490 a h
  have h15 : Entails.eval a c2161 := h 2160 (by decide)
  have h16 : Entails.eval a c1742 := h 1741 (by decide)
  have h17 : Entails.eval a c1747 := h 1746 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8524 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c454, some c434, some c432, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8524 : lratChecker f8524 p8524 = .success := by decide +kernel
theorem unsat8524 : Unsatisfiable (PosFin 65) f8524 := by
  apply lratCheckerSound f8524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8524
  · intro a ha; simp [p8524] at ha; subst a; trivial
  · exact checked8524
theorem derived8524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8524 := by
  apply localUnsat_implies_entails f8524 [c454, c434, c432] c8524 unsat8524 (by rfl) a
  have h0 : Entails.eval a c454 := h 453 (by decide)
  have h1 : Entails.eval a c434 := h 433 (by decide)
  have h2 : Entails.eval a c432 := h 431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8525 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8479, some c8523, some c8524, some c8098, some c8377, some c7961, some c8116, some c518, some c539, some c1972, some c130, some c515, some c2055, some c520, some c2512, some c2269, some c556, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8525 : lratChecker f8525 p8525 = .success := by decide +kernel
theorem unsat8525 : Unsatisfiable (PosFin 65) f8525 := by
  apply lratCheckerSound f8525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8525
  · intro a ha; simp [p8525] at ha; subst a; trivial
  · exact checked8525
theorem derived8525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8525 := by
  apply localUnsat_implies_entails f8525 [c7849, c8479, c8523, c8524, c8098, c8377, c7961, c8116, c518, c539, c1972, c130, c515, c2055, c520, c2512, c2269, c556] c8525 unsat8525 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8479 := derived8479 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8524 := derived8524 a h
  have h4 : Entails.eval a c8098 := derived8098 a h
  have h5 : Entails.eval a c8377 := derived8377 a h
  have h6 : Entails.eval a c7961 := derived7961 a h
  have h7 : Entails.eval a c8116 := derived8116 a h
  have h8 : Entails.eval a c518 := h 517 (by decide)
  have h9 : Entails.eval a c539 := h 538 (by decide)
  have h10 : Entails.eval a c1972 := h 1971 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c515 := h 514 (by decide)
  have h13 : Entails.eval a c2055 := h 2054 (by decide)
  have h14 : Entails.eval a c520 := h 519 (by decide)
  have h15 : Entails.eval a c2512 := h 2511 (by decide)
  have h16 : Entails.eval a c2269 := h 2268 (by decide)
  have h17 : Entails.eval a c556 := h 555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8526 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8479, some c8523, some c8524, some c8098, some c8525, some c8406, some c515, some c2180, some c132, some c8465, some c162, some c2166, some c3416, some c3275, some c1979, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8526 : lratChecker f8526 p8526 = .success := by decide +kernel
theorem unsat8526 : Unsatisfiable (PosFin 65) f8526 := by
  apply lratCheckerSound f8526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8526
  · intro a ha; simp [p8526] at ha; subst a; trivial
  · exact checked8526
theorem derived8526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8526 := by
  apply localUnsat_implies_entails f8526 [c7849, c8479, c8523, c8524, c8098, c8525, c8406, c515, c2180, c132, c8465, c162, c2166, c3416, c3275, c1979] c8526 unsat8526 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8479 := derived8479 a h
  have h2 : Entails.eval a c8523 := derived8523 a h
  have h3 : Entails.eval a c8524 := derived8524 a h
  have h4 : Entails.eval a c8098 := derived8098 a h
  have h5 : Entails.eval a c8525 := derived8525 a h
  have h6 : Entails.eval a c8406 := derived8406 a h
  have h7 : Entails.eval a c515 := h 514 (by decide)
  have h8 : Entails.eval a c2180 := h 2179 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c8465 := derived8465 a h
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c2166 := h 2165 (by decide)
  have h13 : Entails.eval a c3416 := h 3415 (by decide)
  have h14 : Entails.eval a c3275 := h 3274 (by decide)
  have h15 : Entails.eval a c1979 := h 1978 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8527 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8523, some c8479, some c7849, some c8098, some c8524, some c8526, some c1926, some c1912, some c1910, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8527 : lratChecker f8527 p8527 = .success := by decide +kernel
theorem unsat8527 : Unsatisfiable (PosFin 65) f8527 := by
  apply lratCheckerSound f8527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8527
  · intro a ha; simp [p8527] at ha; subst a; trivial
  · exact checked8527
theorem derived8527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8527 := by
  apply localUnsat_implies_entails f8527 [c8523, c8479, c7849, c8098, c8524, c8526, c1926, c1912, c1910] c8527 unsat8527 (by rfl) a
  have h0 : Entails.eval a c8523 := derived8523 a h
  have h1 : Entails.eval a c8479 := derived8479 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8098 := derived8098 a h
  have h4 : Entails.eval a c8524 := derived8524 a h
  have h5 : Entails.eval a c8526 := derived8526 a h
  have h6 : Entails.eval a c1926 := h 1925 (by decide)
  have h7 : Entails.eval a c1912 := h 1911 (by decide)
  have h8 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8528 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8485, some c574, some c566, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8528 : lratChecker f8528 p8528 = .success := by decide +kernel
theorem unsat8528 : Unsatisfiable (PosFin 65) f8528 := by
  apply lratCheckerSound f8528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8528
  · intro a ha; simp [p8528] at ha; subst a; trivial
  · exact checked8528
theorem derived8528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8528 := by
  apply localUnsat_implies_entails f8528 [c8485, c574, c566] c8528 unsat8528 (by rfl) a
  have h0 : Entails.eval a c8485 := derived8485 a h
  have h1 : Entails.eval a c574 := h 573 (by decide)
  have h2 : Entails.eval a c566 := h 565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8529 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1593, some c1823, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8529 : lratChecker f8529 p8529 = .success := by decide +kernel
theorem unsat8529 : Unsatisfiable (PosFin 65) f8529 := by
  apply lratCheckerSound f8529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8529
  · intro a ha; simp [p8529] at ha; subst a; trivial
  · exact checked8529
theorem derived8529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8529 := by
  apply localUnsat_implies_entails f8529 [c1593, c1823] c8529 unsat8529 (by rfl) a
  have h0 : Entails.eval a c1593 := h 1592 (by decide)
  have h1 : Entails.eval a c1823 := h 1822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8530 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8529, some c976, some c944, some c1592, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8530 : lratChecker f8530 p8530 = .success := by decide +kernel
theorem unsat8530 : Unsatisfiable (PosFin 65) f8530 := by
  apply lratCheckerSound f8530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8530
  · intro a ha; simp [p8530] at ha; subst a; trivial
  · exact checked8530
theorem derived8530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8530 := by
  apply localUnsat_implies_entails f8530 [c8529, c976, c944, c1592] c8530 unsat8530 (by rfl) a
  have h0 : Entails.eval a c8529 := derived8529 a h
  have h1 : Entails.eval a c976 := h 975 (by decide)
  have h2 : Entails.eval a c944 := h 943 (by decide)
  have h3 : Entails.eval a c1592 := h 1591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8531 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8490, some c8394, some c8528, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8531 : lratChecker f8531 p8531 = .success := by decide +kernel
theorem unsat8531 : Unsatisfiable (PosFin 65) f8531 := by
  apply lratCheckerSound f8531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8531
  · intro a ha; simp [p8531] at ha; subst a; trivial
  · exact checked8531
theorem derived8531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8531 := by
  apply localUnsat_implies_entails f8531 [c8490, c8394, c8528] c8531 unsat8531 (by rfl) a
  have h0 : Entails.eval a c8490 := derived8490 a h
  have h1 : Entails.eval a c8394 := derived8394 a h
  have h2 : Entails.eval a c8528 := derived8528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8532 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8116, some c8342, some c8530, some c8531, some c8112, some c8120, some c8152, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8532 : lratChecker f8532 p8532 = .success := by decide +kernel
theorem unsat8532 : Unsatisfiable (PosFin 65) f8532 := by
  apply lratCheckerSound f8532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8532
  · intro a ha; simp [p8532] at ha; subst a; trivial
  · exact checked8532
theorem derived8532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8532 := by
  apply localUnsat_implies_entails f8532 [c8116, c8342, c8530, c8531, c8112, c8120, c8152] c8532 unsat8532 (by rfl) a
  have h0 : Entails.eval a c8116 := derived8116 a h
  have h1 : Entails.eval a c8342 := derived8342 a h
  have h2 : Entails.eval a c8530 := derived8530 a h
  have h3 : Entails.eval a c8531 := derived8531 a h
  have h4 : Entails.eval a c8112 := derived8112 a h
  have h5 : Entails.eval a c8120 := derived8120 a h
  have h6 : Entails.eval a c8152 := derived8152 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8533 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8341, some c1497, some c8117, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p8533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8533 : lratChecker f8533 p8533 = .success := by decide +kernel
theorem unsat8533 : Unsatisfiable (PosFin 65) f8533 := by
  apply lratCheckerSound f8533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8533
  · intro a ha; simp [p8533] at ha; subst a; trivial
  · exact checked8533
theorem derived8533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8533 := by
  apply localUnsat_implies_entails f8533 [c8341, c1497, c8117] c8533 unsat8533 (by rfl) a
  have h0 : Entails.eval a c8341 := derived8341 a h
  have h1 : Entails.eval a c1497 := h 1496 (by decide)
  have h2 : Entails.eval a c8117 := derived8117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8534 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8532, some c8533, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8534 : lratChecker f8534 p8534 = .success := by decide +kernel
theorem unsat8534 : Unsatisfiable (PosFin 65) f8534 := by
  apply lratCheckerSound f8534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8534
  · intro a ha; simp [p8534] at ha; subst a; trivial
  · exact checked8534
theorem derived8534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8534 := by
  apply localUnsat_implies_entails f8534 [c8532, c8533] c8534 unsat8534 (by rfl) a
  have h0 : Entails.eval a c8532 := derived8532 a h
  have h1 : Entails.eval a c8533 := derived8533 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8535 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2253, some c676, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8535 : lratChecker f8535 p8535 = .success := by decide +kernel
theorem unsat8535 : Unsatisfiable (PosFin 65) f8535 := by
  apply lratCheckerSound f8535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8535
  · intro a ha; simp [p8535] at ha; subst a; trivial
  · exact checked8535
theorem derived8535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8535 := by
  apply localUnsat_implies_entails f8535 [c2253, c676] c8535 unsat8535 (by rfl) a
  have h0 : Entails.eval a c2253 := h 2252 (by decide)
  have h1 : Entails.eval a c676 := h 675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8536 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2332, some c2386, some c2092, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8536 : lratChecker f8536 p8536 = .success := by decide +kernel
theorem unsat8536 : Unsatisfiable (PosFin 65) f8536 := by
  apply lratCheckerSound f8536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8536
  · intro a ha; simp [p8536] at ha; subst a; trivial
  · exact checked8536
theorem derived8536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8536 := by
  apply localUnsat_implies_entails f8536 [c2332, c2386, c2092] c8536 unsat8536 (by rfl) a
  have h0 : Entails.eval a c2332 := h 2331 (by decide)
  have h1 : Entails.eval a c2386 := h 2385 (by decide)
  have h2 : Entails.eval a c2092 := h 2091 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8537 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2384, some c2218, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8537 : lratChecker f8537 p8537 = .success := by decide +kernel
theorem unsat8537 : Unsatisfiable (PosFin 65) f8537 := by
  apply lratCheckerSound f8537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8537
  · intro a ha; simp [p8537] at ha; subst a; trivial
  · exact checked8537
theorem derived8537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8537 := by
  apply localUnsat_implies_entails f8537 [c2384, c2218] c8537 unsat8537 (by rfl) a
  have h0 : Entails.eval a c2384 := h 2383 (by decide)
  have h1 : Entails.eval a c2218 := h 2217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8538 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8152, some c2331, some c8537, some c471, some c470, some c2089, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8538 : lratChecker f8538 p8538 = .success := by decide +kernel
theorem unsat8538 : Unsatisfiable (PosFin 65) f8538 := by
  apply lratCheckerSound f8538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8538
  · intro a ha; simp [p8538] at ha; subst a; trivial
  · exact checked8538
theorem derived8538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8538 := by
  apply localUnsat_implies_entails f8538 [c8152, c2331, c8537, c471, c470, c2089] c8538 unsat8538 (by rfl) a
  have h0 : Entails.eval a c8152 := derived8152 a h
  have h1 : Entails.eval a c2331 := h 2330 (by decide)
  have h2 : Entails.eval a c8537 := derived8537 a h
  have h3 : Entails.eval a c471 := h 470 (by decide)
  have h4 : Entails.eval a c470 := h 469 (by decide)
  have h5 : Entails.eval a c2089 := h 2088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8539 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8534, some c8536, some c2331, some c8152, some c8535, some c8530, some c8538, some c8503, some c2395, some c2483, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8539 : lratChecker f8539 p8539 = .success := by decide +kernel
theorem unsat8539 : Unsatisfiable (PosFin 65) f8539 := by
  apply lratCheckerSound f8539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8539
  · intro a ha; simp [p8539] at ha; subst a; trivial
  · exact checked8539
theorem derived8539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8539 := by
  apply localUnsat_implies_entails f8539 [c8534, c8536, c2331, c8152, c8535, c8530, c8538, c8503, c2395, c2483] c8539 unsat8539 (by rfl) a
  have h0 : Entails.eval a c8534 := derived8534 a h
  have h1 : Entails.eval a c8536 := derived8536 a h
  have h2 : Entails.eval a c2331 := h 2330 (by decide)
  have h3 : Entails.eval a c8152 := derived8152 a h
  have h4 : Entails.eval a c8535 := derived8535 a h
  have h5 : Entails.eval a c8530 := derived8530 a h
  have h6 : Entails.eval a c8538 := derived8538 a h
  have h7 : Entails.eval a c8503 := derived8503 a h
  have h8 : Entails.eval a c2395 := h 2394 (by decide)
  have h9 : Entails.eval a c2483 := h 2482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8540 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨31, by decide⟩, false), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c693, some c675, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8540 : lratChecker f8540 p8540 = .success := by decide +kernel
theorem unsat8540 : Unsatisfiable (PosFin 65) f8540 := by
  apply lratCheckerSound f8540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8540
  · intro a ha; simp [p8540] at ha; subst a; trivial
  · exact checked8540
theorem derived8540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8540 := by
  apply localUnsat_implies_entails f8540 [c693, c675] c8540 unsat8540 (by rfl) a
  have h0 : Entails.eval a c693 := h 692 (by decide)
  have h1 : Entails.eval a c675 := h 674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8541 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8537, some c471, some c470, some c2089, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8541 : lratChecker f8541 p8541 = .success := by decide +kernel
theorem unsat8541 : Unsatisfiable (PosFin 65) f8541 := by
  apply lratCheckerSound f8541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8541
  · intro a ha; simp [p8541] at ha; subst a; trivial
  · exact checked8541
theorem derived8541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8541 := by
  apply localUnsat_implies_entails f8541 [c8537, c471, c470, c2089] c8541 unsat8541 (by rfl) a
  have h0 : Entails.eval a c8537 := derived8537 a h
  have h1 : Entails.eval a c471 := h 470 (by decide)
  have h2 : Entails.eval a c470 := h 469 (by decide)
  have h3 : Entails.eval a c2089 := h 2088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8542 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8534, some c8536, some c8539, some c2345, some c2265, some c1608, some c581, some c1828, some c8540, some c8541, some c8503, some c2395, some c2483, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8542 : lratChecker f8542 p8542 = .success := by decide +kernel
theorem unsat8542 : Unsatisfiable (PosFin 65) f8542 := by
  apply lratCheckerSound f8542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8542
  · intro a ha; simp [p8542] at ha; subst a; trivial
  · exact checked8542
theorem derived8542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8542 := by
  apply localUnsat_implies_entails f8542 [c8534, c8536, c8539, c2345, c2265, c1608, c581, c1828, c8540, c8541, c8503, c2395, c2483] c8542 unsat8542 (by rfl) a
  have h0 : Entails.eval a c8534 := derived8534 a h
  have h1 : Entails.eval a c8536 := derived8536 a h
  have h2 : Entails.eval a c8539 := derived8539 a h
  have h3 : Entails.eval a c2345 := h 2344 (by decide)
  have h4 : Entails.eval a c2265 := h 2264 (by decide)
  have h5 : Entails.eval a c1608 := h 1607 (by decide)
  have h6 : Entails.eval a c581 := h 580 (by decide)
  have h7 : Entails.eval a c1828 := h 1827 (by decide)
  have h8 : Entails.eval a c8540 := derived8540 a h
  have h9 : Entails.eval a c8541 := derived8541 a h
  have h10 : Entails.eval a c8503 := derived8503 a h
  have h11 : Entails.eval a c2395 := h 2394 (by decide)
  have h12 : Entails.eval a c2483 := h 2482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8543 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8533, some c8116, some c8342, some c2178, some c2163, some c2161, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8543 : lratChecker f8543 p8543 = .success := by decide +kernel
theorem unsat8543 : Unsatisfiable (PosFin 65) f8543 := by
  apply lratCheckerSound f8543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8543
  · intro a ha; simp [p8543] at ha; subst a; trivial
  · exact checked8543
theorem derived8543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8543 := by
  apply localUnsat_implies_entails f8543 [c8533, c8116, c8342, c2178, c2163, c2161] c8543 unsat8543 (by rfl) a
  have h0 : Entails.eval a c8533 := derived8533 a h
  have h1 : Entails.eval a c8116 := derived8116 a h
  have h2 : Entails.eval a c8342 := derived8342 a h
  have h3 : Entails.eval a c2178 := h 2177 (by decide)
  have h4 : Entails.eval a c2163 := h 2162 (by decide)
  have h5 : Entails.eval a c2161 := h 2160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8544 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2254, some c1912, some c569, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8544 : lratChecker f8544 p8544 = .success := by decide +kernel
theorem unsat8544 : Unsatisfiable (PosFin 65) f8544 := by
  apply lratCheckerSound f8544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8544
  · intro a ha; simp [p8544] at ha; subst a; trivial
  · exact checked8544
theorem derived8544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8544 := by
  apply localUnsat_implies_entails f8544 [c2254, c1912, c569] c8544 unsat8544 (by rfl) a
  have h0 : Entails.eval a c2254 := h 2253 (by decide)
  have h1 : Entails.eval a c1912 := h 1911 (by decide)
  have h2 : Entails.eval a c569 := h 568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8545 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8543, some c8336, some c8544, some c8152, some c1910, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p8545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8545 : lratChecker f8545 p8545 = .success := by decide +kernel
theorem unsat8545 : Unsatisfiable (PosFin 65) f8545 := by
  apply lratCheckerSound f8545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8545
  · intro a ha; simp [p8545] at ha; subst a; trivial
  · exact checked8545
theorem derived8545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8545 := by
  apply localUnsat_implies_entails f8545 [c8543, c8336, c8544, c8152, c1910] c8545 unsat8545 (by rfl) a
  have h0 : Entails.eval a c8543 := derived8543 a h
  have h1 : Entails.eval a c8336 := derived8336 a h
  have h2 : Entails.eval a c8544 := derived8544 a h
  have h3 : Entails.eval a c8152 := derived8152 a h
  have h4 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8546 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8542, some c8545, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8546 : lratChecker f8546 p8546 = .success := by decide +kernel
theorem unsat8546 : Unsatisfiable (PosFin 65) f8546 := by
  apply lratCheckerSound f8546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8546
  · intro a ha; simp [p8546] at ha; subst a; trivial
  · exact checked8546
theorem derived8546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8546 := by
  apply localUnsat_implies_entails f8546 [c8542, c8545] c8546 unsat8546 (by rfl) a
  have h0 : Entails.eval a c8542 := derived8542 a h
  have h1 : Entails.eval a c8545 := derived8545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8547 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8479, some c8523, some c8527, some c8546, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8547 : lratChecker f8547 p8547 = .success := by decide +kernel
theorem unsat8547 : Unsatisfiable (PosFin 65) f8547 := by
  apply lratCheckerSound f8547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8547
  · intro a ha; simp [p8547] at ha; subst a; trivial
  · exact checked8547
theorem derived8547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8547 := by
  apply localUnsat_implies_entails f8547 [c8377, c7849, c8479, c8523, c8527, c8546] c8547 unsat8547 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8479 := derived8479 a h
  have h3 : Entails.eval a c8523 := derived8523 a h
  have h4 : Entails.eval a c8527 := derived8527 a h
  have h5 : Entails.eval a c8546 := derived8546 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8548 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c552, some c547, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8548 : lratChecker f8548 p8548 = .success := by decide +kernel
theorem unsat8548 : Unsatisfiable (PosFin 65) f8548 := by
  apply lratCheckerSound f8548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8548
  · intro a ha; simp [p8548] at ha; subst a; trivial
  · exact checked8548
theorem derived8548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8548 := by
  apply localUnsat_implies_entails f8548 [c552, c547] c8548 unsat8548 (by rfl) a
  have h0 : Entails.eval a c552 := h 551 (by decide)
  have h1 : Entails.eval a c547 := h 546 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8549 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c633, some c8446, some c2459, some c2656, some c2653, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8549 : lratChecker f8549 p8549 = .success := by decide +kernel
theorem unsat8549 : Unsatisfiable (PosFin 65) f8549 := by
  apply lratCheckerSound f8549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8549
  · intro a ha; simp [p8549] at ha; subst a; trivial
  · exact checked8549
theorem derived8549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8549 := by
  apply localUnsat_implies_entails f8549 [c633, c8446, c2459, c2656, c2653] c8549 unsat8549 (by rfl) a
  have h0 : Entails.eval a c633 := h 632 (by decide)
  have h1 : Entails.eval a c8446 := derived8446 a h
  have h2 : Entails.eval a c2459 := h 2458 (by decide)
  have h3 : Entails.eval a c2656 := h 2655 (by decide)
  have h4 : Entails.eval a c2653 := h 2652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8550 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8549, some c2659, some c2462, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8550 : lratChecker f8550 p8550 = .success := by decide +kernel
theorem unsat8550 : Unsatisfiable (PosFin 65) f8550 := by
  apply lratCheckerSound f8550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8550
  · intro a ha; simp [p8550] at ha; subst a; trivial
  · exact checked8550
theorem derived8550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8550 := by
  apply localUnsat_implies_entails f8550 [c8549, c2659, c2462] c8550 unsat8550 (by rfl) a
  have h0 : Entails.eval a c8549 := derived8549 a h
  have h1 : Entails.eval a c2659 := h 2658 (by decide)
  have h2 : Entails.eval a c2462 := h 2461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8551 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨31, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8550, some c2488, some c2451, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8551 : lratChecker f8551 p8551 = .success := by decide +kernel
theorem unsat8551 : Unsatisfiable (PosFin 65) f8551 := by
  apply lratCheckerSound f8551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8551
  · intro a ha; simp [p8551] at ha; subst a; trivial
  · exact checked8551
theorem derived8551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8551 := by
  apply localUnsat_implies_entails f8551 [c8550, c2488, c2451] c8551 unsat8551 (by rfl) a
  have h0 : Entails.eval a c8550 := derived8550 a h
  have h1 : Entails.eval a c2488 := h 2487 (by decide)
  have h2 : Entails.eval a c2451 := h 2450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8552 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1878, some c1873, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8552 : lratChecker f8552 p8552 = .success := by decide +kernel
theorem unsat8552 : Unsatisfiable (PosFin 65) f8552 := by
  apply lratCheckerSound f8552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8552
  · intro a ha; simp [p8552] at ha; subst a; trivial
  · exact checked8552
theorem derived8552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8552 := by
  apply localUnsat_implies_entails f8552 [c1878, c1873] c8552 unsat8552 (by rfl) a
  have h0 : Entails.eval a c1878 := h 1877 (by decide)
  have h1 : Entails.eval a c1873 := h 1872 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8553 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c426, some c427, some c8383, some c425, some c8381, some c442, some c446, some c8548, some c429, some c8552, some c7300, some c8551, some c633, some c8234, some c7299, some c7973, some c2549, some c2553, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked8553 : lratChecker f8553 p8553 = .success := by decide +kernel
theorem unsat8553 : Unsatisfiable (PosFin 65) f8553 := by
  apply lratCheckerSound f8553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8553
  · intro a ha; simp [p8553] at ha; subst a; trivial
  · exact checked8553
theorem derived8553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8553 := by
  apply localUnsat_implies_entails f8553 [c426, c427, c8383, c425, c8381, c442, c446, c8548, c429, c8552, c7300, c8551, c633, c8234, c7299, c7973, c2549, c2553] c8553 unsat8553 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c427 := h 426 (by decide)
  have h2 : Entails.eval a c8383 := derived8383 a h
  have h3 : Entails.eval a c425 := h 424 (by decide)
  have h4 : Entails.eval a c8381 := derived8381 a h
  have h5 : Entails.eval a c442 := h 441 (by decide)
  have h6 : Entails.eval a c446 := h 445 (by decide)
  have h7 : Entails.eval a c8548 := derived8548 a h
  have h8 : Entails.eval a c429 := h 428 (by decide)
  have h9 : Entails.eval a c8552 := derived8552 a h
  have h10 : Entails.eval a c7300 := derived7300 a h
  have h11 : Entails.eval a c8551 := derived8551 a h
  have h12 : Entails.eval a c633 := h 632 (by decide)
  have h13 : Entails.eval a c8234 := derived8234 a h
  have h14 : Entails.eval a c7299 := derived7299 a h
  have h15 : Entails.eval a c7973 := derived7973 a h
  have h16 : Entails.eval a c2549 := h 2548 (by decide)
  have h17 : Entails.eval a c2553 := h 2552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8554 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c426, some c425, some c8381, some c442, some c427, some c446, some c429, some c8383, some c8548, some c8552, some c7300, some c8553, some c2488, some c2451, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8554 : lratChecker f8554 p8554 = .success := by decide +kernel
theorem unsat8554 : Unsatisfiable (PosFin 65) f8554 := by
  apply lratCheckerSound f8554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8554
  · intro a ha; simp [p8554] at ha; subst a; trivial
  · exact checked8554
theorem derived8554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8554 := by
  apply localUnsat_implies_entails f8554 [c426, c425, c8381, c442, c427, c446, c429, c8383, c8548, c8552, c7300, c8553, c2488, c2451] c8554 unsat8554 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c425 := h 424 (by decide)
  have h2 : Entails.eval a c8381 := derived8381 a h
  have h3 : Entails.eval a c442 := h 441 (by decide)
  have h4 : Entails.eval a c427 := h 426 (by decide)
  have h5 : Entails.eval a c446 := h 445 (by decide)
  have h6 : Entails.eval a c429 := h 428 (by decide)
  have h7 : Entails.eval a c8383 := derived8383 a h
  have h8 : Entails.eval a c8548 := derived8548 a h
  have h9 : Entails.eval a c8552 := derived8552 a h
  have h10 : Entails.eval a c7300 := derived7300 a h
  have h11 : Entails.eval a c8553 := derived8553 a h
  have h12 : Entails.eval a c2488 := h 2487 (by decide)
  have h13 : Entails.eval a c2451 := h 2450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8555 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2129, some c2360, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p8555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8555 : lratChecker f8555 p8555 = .success := by decide +kernel
theorem unsat8555 : Unsatisfiable (PosFin 65) f8555 := by
  apply lratCheckerSound f8555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8555
  · intro a ha; simp [p8555] at ha; subst a; trivial
  · exact checked8555
theorem derived8555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8555 := by
  apply localUnsat_implies_entails f8555 [c2129, c2360] c8555 unsat8555 (by rfl) a
  have h0 : Entails.eval a c2129 := h 2128 (by decide)
  have h1 : Entails.eval a c2360 := h 2359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8556 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨17, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c853, some c2673, some c1217, some c8241, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8556 : lratChecker f8556 p8556 = .success := by decide +kernel
theorem unsat8556 : Unsatisfiable (PosFin 65) f8556 := by
  apply lratCheckerSound f8556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8556
  · intro a ha; simp [p8556] at ha; subst a; trivial
  · exact checked8556
theorem derived8556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8556 := by
  apply localUnsat_implies_entails f8556 [c853, c2673, c1217, c8241] c8556 unsat8556 (by rfl) a
  have h0 : Entails.eval a c853 := h 852 (by decide)
  have h1 : Entails.eval a c2673 := h 2672 (by decide)
  have h2 : Entails.eval a c1217 := h 1216 (by decide)
  have h3 : Entails.eval a c8241 := derived8241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8557 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c426, some c427, some c8383, some c425, some c8381, some c442, some c446, some c429, some c8554, some c8555, some c8556, some c8552, some c8551, some c7300, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8557 : lratChecker f8557 p8557 = .success := by decide +kernel
theorem unsat8557 : Unsatisfiable (PosFin 65) f8557 := by
  apply lratCheckerSound f8557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8557
  · intro a ha; simp [p8557] at ha; subst a; trivial
  · exact checked8557
theorem derived8557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8557 := by
  apply localUnsat_implies_entails f8557 [c426, c427, c8383, c425, c8381, c442, c446, c429, c8554, c8555, c8556, c8552, c8551, c7300] c8557 unsat8557 (by rfl) a
  have h0 : Entails.eval a c426 := h 425 (by decide)
  have h1 : Entails.eval a c427 := h 426 (by decide)
  have h2 : Entails.eval a c8383 := derived8383 a h
  have h3 : Entails.eval a c425 := h 424 (by decide)
  have h4 : Entails.eval a c8381 := derived8381 a h
  have h5 : Entails.eval a c442 := h 441 (by decide)
  have h6 : Entails.eval a c446 := h 445 (by decide)
  have h7 : Entails.eval a c429 := h 428 (by decide)
  have h8 : Entails.eval a c8554 := derived8554 a h
  have h9 : Entails.eval a c8555 := derived8555 a h
  have h10 : Entails.eval a c8556 := derived8556 a h
  have h11 : Entails.eval a c8552 := derived8552 a h
  have h12 : Entails.eval a c8551 := derived8551 a h
  have h13 : Entails.eval a c7300 := derived7300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8558 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7980, some c608, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8558 : lratChecker f8558 p8558 = .success := by decide +kernel
theorem unsat8558 : Unsatisfiable (PosFin 65) f8558 := by
  apply lratCheckerSound f8558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8558
  · intro a ha; simp [p8558] at ha; subst a; trivial
  · exact checked8558
theorem derived8558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8558 := by
  apply localUnsat_implies_entails f8558 [c7980, c608] c8558 unsat8558 (by rfl) a
  have h0 : Entails.eval a c7980 := derived7980 a h
  have h1 : Entails.eval a c608 := h 607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8559 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨12, by decide⟩, true), (⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c649, some c865, some c419, some c2478, some c6696, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8559 : lratChecker f8559 p8559 = .success := by decide +kernel
theorem unsat8559 : Unsatisfiable (PosFin 65) f8559 := by
  apply lratCheckerSound f8559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8559
  · intro a ha; simp [p8559] at ha; subst a; trivial
  · exact checked8559
theorem derived8559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8559 := by
  apply localUnsat_implies_entails f8559 [c7849, c649, c865, c419, c2478, c6696] c8559 unsat8559 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c649 := h 648 (by decide)
  have h2 : Entails.eval a c865 := h 864 (by decide)
  have h3 : Entails.eval a c419 := h 418 (by decide)
  have h4 : Entails.eval a c2478 := h 2477 (by decide)
  have h5 : Entails.eval a c6696 := derived6696 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8560 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c425, some c8377, some c8381, some c442, some c8234, some c8547, some c427, some c2294, some c2595, some c8559, some c116, some c169, some c171, some c58, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8560 : lratChecker f8560 p8560 = .success := by decide +kernel
theorem unsat8560 : Unsatisfiable (PosFin 65) f8560 := by
  apply lratCheckerSound f8560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8560
  · intro a ha; simp [p8560] at ha; subst a; trivial
  · exact checked8560
theorem derived8560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8560 := by
  apply localUnsat_implies_entails f8560 [c7849, c425, c8377, c8381, c442, c8234, c8547, c427, c2294, c2595, c8559, c116, c169, c171, c58] c8560 unsat8560 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c425 := h 424 (by decide)
  have h2 : Entails.eval a c8377 := derived8377 a h
  have h3 : Entails.eval a c8381 := derived8381 a h
  have h4 : Entails.eval a c442 := h 441 (by decide)
  have h5 : Entails.eval a c8234 := derived8234 a h
  have h6 : Entails.eval a c8547 := derived8547 a h
  have h7 : Entails.eval a c427 := h 426 (by decide)
  have h8 : Entails.eval a c2294 := h 2293 (by decide)
  have h9 : Entails.eval a c2595 := h 2594 (by decide)
  have h10 : Entails.eval a c8559 := derived8559 a h
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8561 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c2303, some c1362, some c1389, some c2604, some c8559, some c170, some c168, some c6712, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8561 : lratChecker f8561 p8561 = .success := by decide +kernel
theorem unsat8561 : Unsatisfiable (PosFin 65) f8561 := by
  apply lratCheckerSound f8561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8561
  · intro a ha; simp [p8561] at ha; subst a; trivial
  · exact checked8561
theorem derived8561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8561 := by
  apply localUnsat_implies_entails f8561 [c8377, c2303, c1362, c1389, c2604, c8559, c170, c168, c6712] c8561 unsat8561 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c2303 := h 2302 (by decide)
  have h2 : Entails.eval a c1362 := h 1361 (by decide)
  have h3 : Entails.eval a c1389 := h 1388 (by decide)
  have h4 : Entails.eval a c2604 := h 2603 (by decide)
  have h5 : Entails.eval a c8559 := derived8559 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c6712 := derived6712 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8562 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c853, some c8547, some c8557, some c426, some c427, some c8383, some c425, some c8381, some c442, some c446, some c429, some c8554, some c8555, some c437, some c8234, some c8558, some c8561, some c2294, some c8560, some c1710, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked8562 : lratChecker f8562 p8562 = .success := by decide +kernel
theorem unsat8562 : Unsatisfiable (PosFin 65) f8562 := by
  apply lratCheckerSound f8562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8562
  · intro a ha; simp [p8562] at ha; subst a; trivial
  · exact checked8562
theorem derived8562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8562 := by
  apply localUnsat_implies_entails f8562 [c8377, c7849, c853, c8547, c8557, c426, c427, c8383, c425, c8381, c442, c446, c429, c8554, c8555, c437, c8234, c8558, c8561, c2294, c8560, c1710] c8562 unsat8562 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c853 := h 852 (by decide)
  have h3 : Entails.eval a c8547 := derived8547 a h
  have h4 : Entails.eval a c8557 := derived8557 a h
  have h5 : Entails.eval a c426 := h 425 (by decide)
  have h6 : Entails.eval a c427 := h 426 (by decide)
  have h7 : Entails.eval a c8383 := derived8383 a h
  have h8 : Entails.eval a c425 := h 424 (by decide)
  have h9 : Entails.eval a c8381 := derived8381 a h
  have h10 : Entails.eval a c442 := h 441 (by decide)
  have h11 : Entails.eval a c446 := h 445 (by decide)
  have h12 : Entails.eval a c429 := h 428 (by decide)
  have h13 : Entails.eval a c8554 := derived8554 a h
  have h14 : Entails.eval a c8555 := derived8555 a h
  have h15 : Entails.eval a c437 := h 436 (by decide)
  have h16 : Entails.eval a c8234 := derived8234 a h
  have h17 : Entails.eval a c8558 := derived8558 a h
  have h18 : Entails.eval a c8561 := derived8561 a h
  have h19 : Entails.eval a c2294 := h 2293 (by decide)
  have h20 : Entails.eval a c8560 := derived8560 a h
  have h21 : Entails.eval a c1710 := h 1709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8563 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8547, some c8554, some c426, some c8383, some c425, some c8562, some c2219, some c2211, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8563 : lratChecker f8563 p8563 = .success := by decide +kernel
theorem unsat8563 : Unsatisfiable (PosFin 65) f8563 := by
  apply lratCheckerSound f8563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8563
  · intro a ha; simp [p8563] at ha; subst a; trivial
  · exact checked8563
theorem derived8563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8563 := by
  apply localUnsat_implies_entails f8563 [c7849, c8377, c8547, c8554, c426, c8383, c425, c8562, c2219, c2211] c8563 unsat8563 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8547 := derived8547 a h
  have h3 : Entails.eval a c8554 := derived8554 a h
  have h4 : Entails.eval a c426 := h 425 (by decide)
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c425 := h 424 (by decide)
  have h7 : Entails.eval a c8562 := derived8562 a h
  have h8 : Entails.eval a c2219 := h 2218 (by decide)
  have h9 : Entails.eval a c2211 := h 2210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8564 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c588, some c972, some c943, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8564 : lratChecker f8564 p8564 = .success := by decide +kernel
theorem unsat8564 : Unsatisfiable (PosFin 65) f8564 := by
  apply lratCheckerSound f8564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8564
  · intro a ha; simp [p8564] at ha; subst a; trivial
  · exact checked8564
theorem derived8564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8564 := by
  apply localUnsat_implies_entails f8564 [c588, c972, c943] c8564 unsat8564 (by rfl) a
  have h0 : Entails.eval a c588 := h 587 (by decide)
  have h1 : Entails.eval a c972 := h 971 (by decide)
  have h2 : Entails.eval a c943 := h 942 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8565 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7300, some c8564, some c601, some c985, some c945, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8565 : lratChecker f8565 p8565 = .success := by decide +kernel
theorem unsat8565 : Unsatisfiable (PosFin 65) f8565 := by
  apply lratCheckerSound f8565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8565
  · intro a ha; simp [p8565] at ha; subst a; trivial
  · exact checked8565
theorem derived8565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8565 := by
  apply localUnsat_implies_entails f8565 [c7300, c8564, c601, c985, c945] c8565 unsat8565 (by rfl) a
  have h0 : Entails.eval a c7300 := derived7300 a h
  have h1 : Entails.eval a c8564 := derived8564 a h
  have h2 : Entails.eval a c601 := h 600 (by decide)
  have h3 : Entails.eval a c985 := h 984 (by decide)
  have h4 : Entails.eval a c945 := h 944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8566 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2219, some c2222, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8566 : lratChecker f8566 p8566 = .success := by decide +kernel
theorem unsat8566 : Unsatisfiable (PosFin 65) f8566 := by
  apply lratCheckerSound f8566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8566
  · intro a ha; simp [p8566] at ha; subst a; trivial
  · exact checked8566
theorem derived8566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8566 := by
  apply localUnsat_implies_entails f8566 [c2219, c2222] c8566 unsat8566 (by rfl) a
  have h0 : Entails.eval a c2219 := h 2218 (by decide)
  have h1 : Entails.eval a c2222 := h 2221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8567 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8547, some c8377, some c7849, some c426, some c8381, some c427, some c425, some c8383, some c442, some c446, some c429, some c8554, some c8555, some c8566, some c633, some c8565, some c8563, some c8552, some c7299, some c2283, some c2298, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked8567 : lratChecker f8567 p8567 = .success := by decide +kernel
theorem unsat8567 : Unsatisfiable (PosFin 65) f8567 := by
  apply lratCheckerSound f8567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8567
  · intro a ha; simp [p8567] at ha; subst a; trivial
  · exact checked8567
theorem derived8567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8567 := by
  apply localUnsat_implies_entails f8567 [c8547, c8377, c7849, c426, c8381, c427, c425, c8383, c442, c446, c429, c8554, c8555, c8566, c633, c8565, c8563, c8552, c7299, c2283, c2298] c8567 unsat8567 (by rfl) a
  have h0 : Entails.eval a c8547 := derived8547 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c426 := h 425 (by decide)
  have h4 : Entails.eval a c8381 := derived8381 a h
  have h5 : Entails.eval a c427 := h 426 (by decide)
  have h6 : Entails.eval a c425 := h 424 (by decide)
  have h7 : Entails.eval a c8383 := derived8383 a h
  have h8 : Entails.eval a c442 := h 441 (by decide)
  have h9 : Entails.eval a c446 := h 445 (by decide)
  have h10 : Entails.eval a c429 := h 428 (by decide)
  have h11 : Entails.eval a c8554 := derived8554 a h
  have h12 : Entails.eval a c8555 := derived8555 a h
  have h13 : Entails.eval a c8566 := derived8566 a h
  have h14 : Entails.eval a c633 := h 632 (by decide)
  have h15 : Entails.eval a c8565 := derived8565 a h
  have h16 : Entails.eval a c8563 := derived8563 a h
  have h17 : Entails.eval a c8552 := derived8552 a h
  have h18 : Entails.eval a c7299 := derived7299 a h
  have h19 : Entails.eval a c2283 := h 2282 (by decide)
  have h20 : Entails.eval a c2298 := h 2297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8568 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c552, some c523, some c842, some c859, some c546, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8568 : lratChecker f8568 p8568 = .success := by decide +kernel
theorem unsat8568 : Unsatisfiable (PosFin 65) f8568 := by
  apply lratCheckerSound f8568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8568
  · intro a ha; simp [p8568] at ha; subst a; trivial
  · exact checked8568
theorem derived8568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8568 := by
  apply localUnsat_implies_entails f8568 [c552, c523, c842, c859, c546] c8568 unsat8568 (by rfl) a
  have h0 : Entails.eval a c552 := h 551 (by decide)
  have h1 : Entails.eval a c523 := h 522 (by decide)
  have h2 : Entails.eval a c842 := h 841 (by decide)
  have h3 : Entails.eval a c859 := h 858 (by decide)
  have h4 : Entails.eval a c546 := h 545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8569 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8568, some c8402, some c633, some c616, some c617, some c7973, some c2171, some c2157, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8569 : lratChecker f8569 p8569 = .success := by decide +kernel
theorem unsat8569 : Unsatisfiable (PosFin 65) f8569 := by
  apply lratCheckerSound f8569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8569
  · intro a ha; simp [p8569] at ha; subst a; trivial
  · exact checked8569
theorem derived8569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8569 := by
  apply localUnsat_implies_entails f8569 [c8568, c8402, c633, c616, c617, c7973, c2171, c2157] c8569 unsat8569 (by rfl) a
  have h0 : Entails.eval a c8568 := derived8568 a h
  have h1 : Entails.eval a c8402 := derived8402 a h
  have h2 : Entails.eval a c633 := h 632 (by decide)
  have h3 : Entails.eval a c616 := h 615 (by decide)
  have h4 : Entails.eval a c617 := h 616 (by decide)
  have h5 : Entails.eval a c7973 := derived7973 a h
  have h6 : Entails.eval a c2171 := h 2170 (by decide)
  have h7 : Entails.eval a c2157 := h 2156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8570 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8568, some c8402, some c8569, some c2012, some c1994, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8570 : lratChecker f8570 p8570 = .success := by decide +kernel
theorem unsat8570 : Unsatisfiable (PosFin 65) f8570 := by
  apply lratCheckerSound f8570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8570
  · intro a ha; simp [p8570] at ha; subst a; trivial
  · exact checked8570
theorem derived8570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8570 := by
  apply localUnsat_implies_entails f8570 [c8568, c8402, c8569, c2012, c1994] c8570 unsat8570 (by rfl) a
  have h0 : Entails.eval a c8568 := derived8568 a h
  have h1 : Entails.eval a c8402 := derived8402 a h
  have h2 : Entails.eval a c8569 := derived8569 a h
  have h3 : Entails.eval a c2012 := h 2011 (by decide)
  have h4 : Entails.eval a c1994 := h 1993 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8571 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8570, some c8455, some c841, some c1942, some c673, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8571 : lratChecker f8571 p8571 = .success := by decide +kernel
theorem unsat8571 : Unsatisfiable (PosFin 65) f8571 := by
  apply lratCheckerSound f8571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8571
  · intro a ha; simp [p8571] at ha; subst a; trivial
  · exact checked8571
theorem derived8571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8571 := by
  apply localUnsat_implies_entails f8571 [c8570, c8455, c841, c1942, c673] c8571 unsat8571 (by rfl) a
  have h0 : Entails.eval a c8570 := derived8570 a h
  have h1 : Entails.eval a c8455 := derived8455 a h
  have h2 : Entails.eval a c841 := h 840 (by decide)
  have h3 : Entails.eval a c1942 := h 1941 (by decide)
  have h4 : Entails.eval a c673 := h 672 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8572 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8447, some c633, some c616, some c8400, some c635, some c627, some c7148, some c564, some c580, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8572 : lratChecker f8572 p8572 = .success := by decide +kernel
theorem unsat8572 : Unsatisfiable (PosFin 65) f8572 := by
  apply lratCheckerSound f8572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8572
  · intro a ha; simp [p8572] at ha; subst a; trivial
  · exact checked8572
theorem derived8572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8572 := by
  apply localUnsat_implies_entails f8572 [c8447, c633, c616, c8400, c635, c627, c7148, c564, c580] c8572 unsat8572 (by rfl) a
  have h0 : Entails.eval a c8447 := derived8447 a h
  have h1 : Entails.eval a c633 := h 632 (by decide)
  have h2 : Entails.eval a c616 := h 615 (by decide)
  have h3 : Entails.eval a c8400 := derived8400 a h
  have h4 : Entails.eval a c635 := h 634 (by decide)
  have h5 : Entails.eval a c627 := h 626 (by decide)
  have h6 : Entails.eval a c7148 := derived7148 a h
  have h7 : Entails.eval a c564 := h 563 (by decide)
  have h8 : Entails.eval a c580 := h 579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8573 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8570, some c8571, some c8402, some c8572, some c1905, some c2012, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8573 : lratChecker f8573 p8573 = .success := by decide +kernel
theorem unsat8573 : Unsatisfiable (PosFin 65) f8573 := by
  apply lratCheckerSound f8573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8573
  · intro a ha; simp [p8573] at ha; subst a; trivial
  · exact checked8573
theorem derived8573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8573 := by
  apply localUnsat_implies_entails f8573 [c8570, c8571, c8402, c8572, c1905, c2012] c8573 unsat8573 (by rfl) a
  have h0 : Entails.eval a c8570 := derived8570 a h
  have h1 : Entails.eval a c8571 := derived8571 a h
  have h2 : Entails.eval a c8402 := derived8402 a h
  have h3 : Entails.eval a c8572 := derived8572 a h
  have h4 : Entails.eval a c1905 := h 1904 (by decide)
  have h5 : Entails.eval a c2012 := h 2011 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8574 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8547, some c8377, some c7849, some c8567, some c8573, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8574 : lratChecker f8574 p8574 = .success := by decide +kernel
theorem unsat8574 : Unsatisfiable (PosFin 65) f8574 := by
  apply lratCheckerSound f8574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8574
  · intro a ha; simp [p8574] at ha; subst a; trivial
  · exact checked8574
theorem derived8574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8574 := by
  apply localUnsat_implies_entails f8574 [c8547, c8377, c7849, c8567, c8573] c8574 unsat8574 (by rfl) a
  have h0 : Entails.eval a c8547 := derived8547 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8567 := derived8567 a h
  have h4 : Entails.eval a c8573 := derived8573 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8575 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c526, some c517, some c537, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8575 : lratChecker f8575 p8575 = .success := by decide +kernel
theorem unsat8575 : Unsatisfiable (PosFin 65) f8575 := by
  apply lratCheckerSound f8575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8575
  · intro a ha; simp [p8575] at ha; subst a; trivial
  · exact checked8575
theorem derived8575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8575 := by
  apply localUnsat_implies_entails f8575 [c526, c517, c537] c8575 unsat8575 (by rfl) a
  have h0 : Entails.eval a c526 := h 525 (by decide)
  have h1 : Entails.eval a c517 := h 516 (by decide)
  have h2 : Entails.eval a c537 := h 536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8576 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8575, some c839, some c524, some c525, some c854, some c857, some c538, some c848, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8576 : lratChecker f8576 p8576 = .success := by decide +kernel
theorem unsat8576 : Unsatisfiable (PosFin 65) f8576 := by
  apply lratCheckerSound f8576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8576
  · intro a ha; simp [p8576] at ha; subst a; trivial
  · exact checked8576
theorem derived8576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8576 := by
  apply localUnsat_implies_entails f8576 [c8575, c839, c524, c525, c854, c857, c538, c848] c8576 unsat8576 (by rfl) a
  have h0 : Entails.eval a c8575 := derived8575 a h
  have h1 : Entails.eval a c839 := h 838 (by decide)
  have h2 : Entails.eval a c524 := h 523 (by decide)
  have h3 : Entails.eval a c525 := h 524 (by decide)
  have h4 : Entails.eval a c854 := h 853 (by decide)
  have h5 : Entails.eval a c857 := h 856 (by decide)
  have h6 : Entails.eval a c538 := h 537 (by decide)
  have h7 : Entails.eval a c848 := h 847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8577 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1989, some c1995, some c2003, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p8577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8577 : lratChecker f8577 p8577 = .success := by decide +kernel
theorem unsat8577 : Unsatisfiable (PosFin 65) f8577 := by
  apply lratCheckerSound f8577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8577
  · intro a ha; simp [p8577] at ha; subst a; trivial
  · exact checked8577
theorem derived8577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8577 := by
  apply localUnsat_implies_entails f8577 [c1989, c1995, c2003] c8577 unsat8577 (by rfl) a
  have h0 : Entails.eval a c1989 := h 1988 (by decide)
  have h1 : Entails.eval a c1995 := h 1994 (by decide)
  have h2 : Entails.eval a c2003 := h 2002 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8578 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1990, some c1993, some c1994, some c2007, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p8578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8578 : lratChecker f8578 p8578 = .success := by decide +kernel
theorem unsat8578 : Unsatisfiable (PosFin 65) f8578 := by
  apply lratCheckerSound f8578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8578
  · intro a ha; simp [p8578] at ha; subst a; trivial
  · exact checked8578
theorem derived8578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8578 := by
  apply localUnsat_implies_entails f8578 [c1990, c1993, c1994, c2007] c8578 unsat8578 (by rfl) a
  have h0 : Entails.eval a c1990 := h 1989 (by decide)
  have h1 : Entails.eval a c1993 := h 1992 (by decide)
  have h2 : Entails.eval a c1994 := h 1993 (by decide)
  have h3 : Entails.eval a c2007 := h 2006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8579 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8547, some c8377, some c7849, some c8574, some c8445, some c8395, some c8405, some c8576, some c8577, some c8578, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8579 : lratChecker f8579 p8579 = .success := by decide +kernel
theorem unsat8579 : Unsatisfiable (PosFin 65) f8579 := by
  apply lratCheckerSound f8579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8579
  · intro a ha; simp [p8579] at ha; subst a; trivial
  · exact checked8579
theorem derived8579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8579 := by
  apply localUnsat_implies_entails f8579 [c8547, c8377, c7849, c8574, c8445, c8395, c8405, c8576, c8577, c8578] c8579 unsat8579 (by rfl) a
  have h0 : Entails.eval a c8547 := derived8547 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8574 := derived8574 a h
  have h4 : Entails.eval a c8445 := derived8445 a h
  have h5 : Entails.eval a c8395 := derived8395 a h
  have h6 : Entails.eval a c8405 := derived8405 a h
  have h7 : Entails.eval a c8576 := derived8576 a h
  have h8 : Entails.eval a c8577 := derived8577 a h
  have h9 : Entails.eval a c8578 := derived8578 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8580 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c552, some c523, some c525, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8580 : lratChecker f8580 p8580 = .success := by decide +kernel
theorem unsat8580 : Unsatisfiable (PosFin 65) f8580 := by
  apply lratCheckerSound f8580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8580
  · intro a ha; simp [p8580] at ha; subst a; trivial
  · exact checked8580
theorem derived8580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8580 := by
  apply localUnsat_implies_entails f8580 [c552, c523, c525] c8580 unsat8580 (by rfl) a
  have h0 : Entails.eval a c552 := h 551 (by decide)
  have h1 : Entails.eval a c523 := h 522 (by decide)
  have h2 : Entails.eval a c525 := h 524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived8580

end CochromaticTwenty.Certificates.FixedCore1
