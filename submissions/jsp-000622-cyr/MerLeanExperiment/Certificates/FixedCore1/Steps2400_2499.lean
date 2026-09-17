import MerLeanExperiment.Certificates.FixedCore1.Steps2300_2399

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8281 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2271, some c1016, some c2608, some c1031, some c602, some c513, some c603, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8281 : lratChecker f8281 p8281 = .success := by decide +kernel
theorem unsat8281 : Unsatisfiable (PosFin 65) f8281 := by
  apply lratCheckerSound f8281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8281
  · intro a ha; simp [p8281] at ha; subst a; trivial
  · exact checked8281
theorem derived8281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8281 := by
  apply localUnsat_implies_entails f8281 [c2271, c1016, c2608, c1031, c602, c513, c603] c8281 unsat8281 (by rfl) a
  have h0 : Entails.eval a c2271 := h 2270 (by decide)
  have h1 : Entails.eval a c1016 := h 1015 (by decide)
  have h2 : Entails.eval a c2608 := h 2607 (by decide)
  have h3 : Entails.eval a c1031 := h 1030 (by decide)
  have h4 : Entails.eval a c602 := h 601 (by decide)
  have h5 : Entails.eval a c513 := h 512 (by decide)
  have h6 : Entails.eval a c603 := h 602 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8282 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8256, some c1595, some c474, some c1853, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8282 : lratChecker f8282 p8282 = .success := by decide +kernel
theorem unsat8282 : Unsatisfiable (PosFin 65) f8282 := by
  apply lratCheckerSound f8282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8282
  · intro a ha; simp [p8282] at ha; subst a; trivial
  · exact checked8282
theorem derived8282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8282 := by
  apply localUnsat_implies_entails f8282 [c8256, c1595, c474, c1853] c8282 unsat8282 (by rfl) a
  have h0 : Entails.eval a c8256 := derived8256 a h
  have h1 : Entails.eval a c1595 := h 1594 (by decide)
  have h2 : Entails.eval a c474 := h 473 (by decide)
  have h3 : Entails.eval a c1853 := h 1852 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8283 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1963, some c2073, some c2062, some c2455, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p8283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8283 : lratChecker f8283 p8283 = .success := by decide +kernel
theorem unsat8283 : Unsatisfiable (PosFin 65) f8283 := by
  apply lratCheckerSound f8283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8283
  · intro a ha; simp [p8283] at ha; subst a; trivial
  · exact checked8283
theorem derived8283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8283 := by
  apply localUnsat_implies_entails f8283 [c1963, c2073, c2062, c2455] c8283 unsat8283 (by rfl) a
  have h0 : Entails.eval a c1963 := h 1962 (by decide)
  have h1 : Entails.eval a c2073 := h 2072 (by decide)
  have h2 : Entails.eval a c2062 := h 2061 (by decide)
  have h3 : Entails.eval a c2455 := h 2454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8284 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c544, some c8281, some c533, some c530, some c8282, some c2275, some c8283, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8284 : lratChecker f8284 p8284 = .success := by decide +kernel
theorem unsat8284 : Unsatisfiable (PosFin 65) f8284 := by
  apply lratCheckerSound f8284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8284
  · intro a ha; simp [p8284] at ha; subst a; trivial
  · exact checked8284
theorem derived8284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8284 := by
  apply localUnsat_implies_entails f8284 [c545, c553, c544, c8281, c533, c530, c8282, c2275, c8283] c8284 unsat8284 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c544 := h 543 (by decide)
  have h3 : Entails.eval a c8281 := derived8281 a h
  have h4 : Entails.eval a c533 := h 532 (by decide)
  have h5 : Entails.eval a c530 := h 529 (by decide)
  have h6 : Entails.eval a c8282 := derived8282 a h
  have h7 : Entails.eval a c2275 := h 2274 (by decide)
  have h8 : Entails.eval a c8283 := derived8283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8285 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2097, some c1598, some c1882, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8285 : lratChecker f8285 p8285 = .success := by decide +kernel
theorem unsat8285 : Unsatisfiable (PosFin 65) f8285 := by
  apply lratCheckerSound f8285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8285
  · intro a ha; simp [p8285] at ha; subst a; trivial
  · exact checked8285
theorem derived8285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8285 := by
  apply localUnsat_implies_entails f8285 [c2097, c1598, c1882] c8285 unsat8285 (by rfl) a
  have h0 : Entails.eval a c2097 := h 2096 (by decide)
  have h1 : Entails.eval a c1598 := h 1597 (by decide)
  have h2 : Entails.eval a c1882 := h 1881 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8286 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c484, some c2098, some c472, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8286 : lratChecker f8286 p8286 = .success := by decide +kernel
theorem unsat8286 : Unsatisfiable (PosFin 65) f8286 := by
  apply lratCheckerSound f8286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8286
  · intro a ha; simp [p8286] at ha; subst a; trivial
  · exact checked8286
theorem derived8286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8286 := by
  apply localUnsat_implies_entails f8286 [c484, c2098, c472] c8286 unsat8286 (by rfl) a
  have h0 : Entails.eval a c484 := h 483 (by decide)
  have h1 : Entails.eval a c2098 := h 2097 (by decide)
  have h2 : Entails.eval a c472 := h 471 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8287 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8166, some c2499, some c1371, some c893, some c1214, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8287 : lratChecker f8287 p8287 = .success := by decide +kernel
theorem unsat8287 : Unsatisfiable (PosFin 65) f8287 := by
  apply lratCheckerSound f8287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8287
  · intro a ha; simp [p8287] at ha; subst a; trivial
  · exact checked8287
theorem derived8287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8287 := by
  apply localUnsat_implies_entails f8287 [c8166, c2499, c1371, c893, c1214] c8287 unsat8287 (by rfl) a
  have h0 : Entails.eval a c8166 := derived8166 a h
  have h1 : Entails.eval a c2499 := h 2498 (by decide)
  have h2 : Entails.eval a c1371 := h 1370 (by decide)
  have h3 : Entails.eval a c893 := h 892 (by decide)
  have h4 : Entails.eval a c1214 := h 1213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8288 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2659, some c1852, some c2481, some c1681, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p8288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8288 : lratChecker f8288 p8288 = .success := by decide +kernel
theorem unsat8288 : Unsatisfiable (PosFin 65) f8288 := by
  apply lratCheckerSound f8288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8288
  · intro a ha; simp [p8288] at ha; subst a; trivial
  · exact checked8288
theorem derived8288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8288 := by
  apply localUnsat_implies_entails f8288 [c2659, c1852, c2481, c1681] c8288 unsat8288 (by rfl) a
  have h0 : Entails.eval a c2659 := h 2658 (by decide)
  have h1 : Entails.eval a c1852 := h 1851 (by decide)
  have h2 : Entails.eval a c2481 := h 2480 (by decide)
  have h3 : Entails.eval a c1681 := h 1680 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8289 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c509, some c513, some c1596, some c1859, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8289 : lratChecker f8289 p8289 = .success := by decide +kernel
theorem unsat8289 : Unsatisfiable (PosFin 65) f8289 := by
  apply lratCheckerSound f8289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8289
  · intro a ha; simp [p8289] at ha; subst a; trivial
  · exact checked8289
theorem derived8289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8289 := by
  apply localUnsat_implies_entails f8289 [c509, c513, c1596, c1859] c8289 unsat8289 (by rfl) a
  have h0 : Entails.eval a c509 := h 508 (by decide)
  have h1 : Entails.eval a c513 := h 512 (by decide)
  have h2 : Entails.eval a c1596 := h 1595 (by decide)
  have h3 : Entails.eval a c1859 := h 1858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8290 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨31, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1837, some c2575, some c2666, some c2497, some c1659, some c1668, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8290 : lratChecker f8290 p8290 = .success := by decide +kernel
theorem unsat8290 : Unsatisfiable (PosFin 65) f8290 := by
  apply lratCheckerSound f8290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8290
  · intro a ha; simp [p8290] at ha; subst a; trivial
  · exact checked8290
theorem derived8290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8290 := by
  apply localUnsat_implies_entails f8290 [c1837, c2575, c2666, c2497, c1659, c1668] c8290 unsat8290 (by rfl) a
  have h0 : Entails.eval a c1837 := h 1836 (by decide)
  have h1 : Entails.eval a c2575 := h 2574 (by decide)
  have h2 : Entails.eval a c2666 := h 2665 (by decide)
  have h3 : Entails.eval a c2497 := h 2496 (by decide)
  have h4 : Entails.eval a c1659 := h 1658 (by decide)
  have h5 : Entails.eval a c1668 := h 1667 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8291 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8284, some c8285, some c8286, some c8287, some c8288, some c8289, some c8290, some c1605, some c1862, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8291 : lratChecker f8291 p8291 = .success := by decide +kernel
theorem unsat8291 : Unsatisfiable (PosFin 65) f8291 := by
  apply lratCheckerSound f8291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8291
  · intro a ha; simp [p8291] at ha; subst a; trivial
  · exact checked8291
theorem derived8291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8291 := by
  apply localUnsat_implies_entails f8291 [c8284, c8285, c8286, c8287, c8288, c8289, c8290, c1605, c1862] c8291 unsat8291 (by rfl) a
  have h0 : Entails.eval a c8284 := derived8284 a h
  have h1 : Entails.eval a c8285 := derived8285 a h
  have h2 : Entails.eval a c8286 := derived8286 a h
  have h3 : Entails.eval a c8287 := derived8287 a h
  have h4 : Entails.eval a c8288 := derived8288 a h
  have h5 : Entails.eval a c8289 := derived8289 a h
  have h6 : Entails.eval a c8290 := derived8290 a h
  have h7 : Entails.eval a c1605 := h 1604 (by decide)
  have h8 : Entails.eval a c1862 := h 1861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8292 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1600, some c1595, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8292 : lratChecker f8292 p8292 = .success := by decide +kernel
theorem unsat8292 : Unsatisfiable (PosFin 65) f8292 := by
  apply lratCheckerSound f8292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8292
  · intro a ha; simp [p8292] at ha; subst a; trivial
  · exact checked8292
theorem derived8292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8292 := by
  apply localUnsat_implies_entails f8292 [c1600, c1595] c8292 unsat8292 (by rfl) a
  have h0 : Entails.eval a c1600 := h 1599 (by decide)
  have h1 : Entails.eval a c1595 := h 1594 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8293 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8284, some c8285, some c8286, some c8291, some c8292, some c1860, some c1886, some c1880, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8293 : lratChecker f8293 p8293 = .success := by decide +kernel
theorem unsat8293 : Unsatisfiable (PosFin 65) f8293 := by
  apply lratCheckerSound f8293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8293
  · intro a ha; simp [p8293] at ha; subst a; trivial
  · exact checked8293
theorem derived8293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8293 := by
  apply localUnsat_implies_entails f8293 [c8284, c8285, c8286, c8291, c8292, c1860, c1886, c1880] c8293 unsat8293 (by rfl) a
  have h0 : Entails.eval a c8284 := derived8284 a h
  have h1 : Entails.eval a c8285 := derived8285 a h
  have h2 : Entails.eval a c8286 := derived8286 a h
  have h3 : Entails.eval a c8291 := derived8291 a h
  have h4 : Entails.eval a c8292 := derived8292 a h
  have h5 : Entails.eval a c1860 := h 1859 (by decide)
  have h6 : Entails.eval a c1886 := h 1885 (by decide)
  have h7 : Entails.eval a c1880 := h 1879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8294 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8159, some c8221, some c8269, some c8280, some c8293, some c8284, some c2008, some c576, some c1403, some c139, some c8149, some c3343, some c3345, some c8049, some c2040, some c1322, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8294 : lratChecker f8294 p8294 = .success := by decide +kernel
theorem unsat8294 : Unsatisfiable (PosFin 65) f8294 := by
  apply lratCheckerSound f8294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8294
  · intro a ha; simp [p8294] at ha; subst a; trivial
  · exact checked8294
theorem derived8294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8294 := by
  apply localUnsat_implies_entails f8294 [c7849, c8159, c8221, c8269, c8280, c8293, c8284, c2008, c576, c1403, c139, c8149, c3343, c3345, c8049, c2040, c1322] c8294 unsat8294 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c8221 := derived8221 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c8280 := derived8280 a h
  have h5 : Entails.eval a c8293 := derived8293 a h
  have h6 : Entails.eval a c8284 := derived8284 a h
  have h7 : Entails.eval a c2008 := h 2007 (by decide)
  have h8 : Entails.eval a c576 := h 575 (by decide)
  have h9 : Entails.eval a c1403 := h 1402 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c8149 := derived8149 a h
  have h12 : Entails.eval a c3343 := h 3342 (by decide)
  have h13 : Entails.eval a c3345 := h 3344 (by decide)
  have h14 : Entails.eval a c8049 := derived8049 a h
  have h15 : Entails.eval a c2040 := h 2039 (by decide)
  have h16 : Entails.eval a c1322 := h 1321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8295 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1985, some c2146, some c608, some c831, some c830, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8295 : lratChecker f8295 p8295 = .success := by decide +kernel
theorem unsat8295 : Unsatisfiable (PosFin 65) f8295 := by
  apply lratCheckerSound f8295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8295
  · intro a ha; simp [p8295] at ha; subst a; trivial
  · exact checked8295
theorem derived8295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8295 := by
  apply localUnsat_implies_entails f8295 [c1985, c2146, c608, c831, c830] c8295 unsat8295 (by rfl) a
  have h0 : Entails.eval a c1985 := h 1984 (by decide)
  have h1 : Entails.eval a c2146 := h 2145 (by decide)
  have h2 : Entails.eval a c608 := h 607 (by decide)
  have h3 : Entails.eval a c831 := h 830 (by decide)
  have h4 : Entails.eval a c830 := h 829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8296 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨15, by decide⟩, true), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8295, some c8166, some c1463, some c8079, some c8151, some c1555, some c2607, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8296 : lratChecker f8296 p8296 = .success := by decide +kernel
theorem unsat8296 : Unsatisfiable (PosFin 65) f8296 := by
  apply lratCheckerSound f8296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8296
  · intro a ha; simp [p8296] at ha; subst a; trivial
  · exact checked8296
theorem derived8296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8296 := by
  apply localUnsat_implies_entails f8296 [c8295, c8166, c1463, c8079, c8151, c1555, c2607] c8296 unsat8296 (by rfl) a
  have h0 : Entails.eval a c8295 := derived8295 a h
  have h1 : Entails.eval a c8166 := derived8166 a h
  have h2 : Entails.eval a c1463 := h 1462 (by decide)
  have h3 : Entails.eval a c8079 := derived8079 a h
  have h4 : Entails.eval a c8151 := derived8151 a h
  have h5 : Entails.eval a c1555 := h 1554 (by decide)
  have h6 : Entails.eval a c2607 := h 2606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8297 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8296, some c7926, some c2178, some c2170, some c667, some c2577, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8297 : lratChecker f8297 p8297 = .success := by decide +kernel
theorem unsat8297 : Unsatisfiable (PosFin 65) f8297 := by
  apply lratCheckerSound f8297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8297
  · intro a ha; simp [p8297] at ha; subst a; trivial
  · exact checked8297
theorem derived8297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8297 := by
  apply localUnsat_implies_entails f8297 [c8296, c7926, c2178, c2170, c667, c2577] c8297 unsat8297 (by rfl) a
  have h0 : Entails.eval a c8296 := derived8296 a h
  have h1 : Entails.eval a c7926 := derived7926 a h
  have h2 : Entails.eval a c2178 := h 2177 (by decide)
  have h3 : Entails.eval a c2170 := h 2169 (by decide)
  have h4 : Entails.eval a c667 := h 666 (by decide)
  have h5 : Entails.eval a c2577 := h 2576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8298 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨15, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2014, some c2125, some c1886, some c1697, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8298 : lratChecker f8298 p8298 = .success := by decide +kernel
theorem unsat8298 : Unsatisfiable (PosFin 65) f8298 := by
  apply lratCheckerSound f8298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8298
  · intro a ha; simp [p8298] at ha; subst a; trivial
  · exact checked8298
theorem derived8298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8298 := by
  apply localUnsat_implies_entails f8298 [c2014, c2125, c1886, c1697] c8298 unsat8298 (by rfl) a
  have h0 : Entails.eval a c2014 := h 2013 (by decide)
  have h1 : Entails.eval a c2125 := h 2124 (by decide)
  have h2 : Entails.eval a c1886 := h 1885 (by decide)
  have h3 : Entails.eval a c1697 := h 1696 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8299 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c509, some c513, some c497, some c2349, some c2664, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8299 : lratChecker f8299 p8299 = .success := by decide +kernel
theorem unsat8299 : Unsatisfiable (PosFin 65) f8299 := by
  apply lratCheckerSound f8299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8299
  · intro a ha; simp [p8299] at ha; subst a; trivial
  · exact checked8299
theorem derived8299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8299 := by
  apply localUnsat_implies_entails f8299 [c509, c513, c497, c2349, c2664] c8299 unsat8299 (by rfl) a
  have h0 : Entails.eval a c509 := h 508 (by decide)
  have h1 : Entails.eval a c513 := h 512 (by decide)
  have h2 : Entails.eval a c497 := h 496 (by decide)
  have h3 : Entails.eval a c2349 := h 2348 (by decide)
  have h4 : Entails.eval a c2664 := h 2663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8300 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8297, some c8298, some c8288, some c8299, some c2163, some c2141, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8300 : lratChecker f8300 p8300 = .success := by decide +kernel
theorem unsat8300 : Unsatisfiable (PosFin 65) f8300 := by
  apply lratCheckerSound f8300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8300
  · intro a ha; simp [p8300] at ha; subst a; trivial
  · exact checked8300
theorem derived8300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8300 := by
  apply localUnsat_implies_entails f8300 [c8297, c8298, c8288, c8299, c2163, c2141] c8300 unsat8300 (by rfl) a
  have h0 : Entails.eval a c8297 := derived8297 a h
  have h1 : Entails.eval a c8298 := derived8298 a h
  have h2 : Entails.eval a c8288 := derived8288 a h
  have h3 : Entails.eval a c8299 := derived8299 a h
  have h4 : Entails.eval a c2163 := h 2162 (by decide)
  have h5 : Entails.eval a c2141 := h 2140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8301 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8295, some c668, some c142, some c1404, some c6775, some c6774, some c8080, some c1555, some c2139, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8301 : lratChecker f8301 p8301 = .success := by decide +kernel
theorem unsat8301 : Unsatisfiable (PosFin 65) f8301 := by
  apply lratCheckerSound f8301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8301
  · intro a ha; simp [p8301] at ha; subst a; trivial
  · exact checked8301
theorem derived8301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8301 := by
  apply localUnsat_implies_entails f8301 [c8295, c668, c142, c1404, c6775, c6774, c8080, c1555, c2139] c8301 unsat8301 (by rfl) a
  have h0 : Entails.eval a c8295 := derived8295 a h
  have h1 : Entails.eval a c668 := h 667 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c1404 := h 1403 (by decide)
  have h4 : Entails.eval a c6775 := derived6775 a h
  have h5 : Entails.eval a c6774 := derived6774 a h
  have h6 : Entails.eval a c8080 := derived8080 a h
  have h7 : Entails.eval a c1555 := h 1554 (by decide)
  have h8 : Entails.eval a c2139 := h 2138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8302 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2175, some c2169, some c2177, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8302 : lratChecker f8302 p8302 = .success := by decide +kernel
theorem unsat8302 : Unsatisfiable (PosFin 65) f8302 := by
  apply lratCheckerSound f8302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8302
  · intro a ha; simp [p8302] at ha; subst a; trivial
  · exact checked8302
theorem derived8302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8302 := by
  apply localUnsat_implies_entails f8302 [c2175, c2169, c2177] c8302 unsat8302 (by rfl) a
  have h0 : Entails.eval a c2175 := h 2174 (by decide)
  have h1 : Entails.eval a c2169 := h 2168 (by decide)
  have h2 : Entails.eval a c2177 := h 2176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8303 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8284, some c8293, some c8300, some c8302, some c8301, some c832, some c8276, some c2649, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8303 : lratChecker f8303 p8303 = .success := by decide +kernel
theorem unsat8303 : Unsatisfiable (PosFin 65) f8303 := by
  apply lratCheckerSound f8303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8303
  · intro a ha; simp [p8303] at ha; subst a; trivial
  · exact checked8303
theorem derived8303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8303 := by
  apply localUnsat_implies_entails f8303 [c8284, c8293, c8300, c8302, c8301, c832, c8276, c2649] c8303 unsat8303 (by rfl) a
  have h0 : Entails.eval a c8284 := derived8284 a h
  have h1 : Entails.eval a c8293 := derived8293 a h
  have h2 : Entails.eval a c8300 := derived8300 a h
  have h3 : Entails.eval a c8302 := derived8302 a h
  have h4 : Entails.eval a c8301 := derived8301 a h
  have h5 : Entails.eval a c832 := h 831 (by decide)
  have h6 : Entails.eval a c8276 := derived8276 a h
  have h7 : Entails.eval a c2649 := h 2648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8304 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8288, some c2013, some c1886, some c491, some c1722, some c7530, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8304 : lratChecker f8304 p8304 = .success := by decide +kernel
theorem unsat8304 : Unsatisfiable (PosFin 65) f8304 := by
  apply lratCheckerSound f8304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8304
  · intro a ha; simp [p8304] at ha; subst a; trivial
  · exact checked8304
theorem derived8304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8304 := by
  apply localUnsat_implies_entails f8304 [c8288, c2013, c1886, c491, c1722, c7530] c8304 unsat8304 (by rfl) a
  have h0 : Entails.eval a c8288 := derived8288 a h
  have h1 : Entails.eval a c2013 := h 2012 (by decide)
  have h2 : Entails.eval a c1886 := h 1885 (by decide)
  have h3 : Entails.eval a c491 := h 490 (by decide)
  have h4 : Entails.eval a c1722 := h 1721 (by decide)
  have h5 : Entails.eval a c7530 := derived7530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8305 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8280, some c8269, some c8221, some c8159, some c7849, some c8284, some c8293, some c8294, some c8300, some c8302, some c8303, some c8304, some c509, some c513, some c2632, some c2664, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8305 : lratChecker f8305 p8305 = .success := by decide +kernel
theorem unsat8305 : Unsatisfiable (PosFin 65) f8305 := by
  apply lratCheckerSound f8305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8305
  · intro a ha; simp [p8305] at ha; subst a; trivial
  · exact checked8305
theorem derived8305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8305 := by
  apply localUnsat_implies_entails f8305 [c8280, c8269, c8221, c8159, c7849, c8284, c8293, c8294, c8300, c8302, c8303, c8304, c509, c513, c2632, c2664] c8305 unsat8305 (by rfl) a
  have h0 : Entails.eval a c8280 := derived8280 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c8221 := derived8221 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8284 := derived8284 a h
  have h6 : Entails.eval a c8293 := derived8293 a h
  have h7 : Entails.eval a c8294 := derived8294 a h
  have h8 : Entails.eval a c8300 := derived8300 a h
  have h9 : Entails.eval a c8302 := derived8302 a h
  have h10 : Entails.eval a c8303 := derived8303 a h
  have h11 : Entails.eval a c8304 := derived8304 a h
  have h12 : Entails.eval a c509 := h 508 (by decide)
  have h13 : Entails.eval a c513 := h 512 (by decide)
  have h14 : Entails.eval a c2632 := h 2631 (by decide)
  have h15 : Entails.eval a c2664 := h 2663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8306 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c685, some c8256, some c2263, some c2241, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8306 : lratChecker f8306 p8306 = .success := by decide +kernel
theorem unsat8306 : Unsatisfiable (PosFin 65) f8306 := by
  apply lratCheckerSound f8306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8306
  · intro a ha; simp [p8306] at ha; subst a; trivial
  · exact checked8306
theorem derived8306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8306 := by
  apply localUnsat_implies_entails f8306 [c685, c8256, c2263, c2241] c8306 unsat8306 (by rfl) a
  have h0 : Entails.eval a c685 := h 684 (by decide)
  have h1 : Entails.eval a c8256 := derived8256 a h
  have h2 : Entails.eval a c2263 := h 2262 (by decide)
  have h3 : Entails.eval a c2241 := h 2240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8307 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8306, some c8286, some c2399, some c2404, some c2373, some c1858, some c2397, some c1605, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8307 : lratChecker f8307 p8307 = .success := by decide +kernel
theorem unsat8307 : Unsatisfiable (PosFin 65) f8307 := by
  apply lratCheckerSound f8307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8307
  · intro a ha; simp [p8307] at ha; subst a; trivial
  · exact checked8307
theorem derived8307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8307 := by
  apply localUnsat_implies_entails f8307 [c8306, c8286, c2399, c2404, c2373, c1858, c2397, c1605] c8307 unsat8307 (by rfl) a
  have h0 : Entails.eval a c8306 := derived8306 a h
  have h1 : Entails.eval a c8286 := derived8286 a h
  have h2 : Entails.eval a c2399 := h 2398 (by decide)
  have h3 : Entails.eval a c2404 := h 2403 (by decide)
  have h4 : Entails.eval a c2373 := h 2372 (by decide)
  have h5 : Entails.eval a c1858 := h 1857 (by decide)
  have h6 : Entails.eval a c2397 := h 2396 (by decide)
  have h7 : Entails.eval a c1605 := h 1604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8308 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1954, some c2263, some c2241, some c1933, some c2259, some c2252, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8308 : lratChecker f8308 p8308 = .success := by decide +kernel
theorem unsat8308 : Unsatisfiable (PosFin 65) f8308 := by
  apply lratCheckerSound f8308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8308
  · intro a ha; simp [p8308] at ha; subst a; trivial
  · exact checked8308
theorem derived8308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8308 := by
  apply localUnsat_implies_entails f8308 [c1954, c2263, c2241, c1933, c2259, c2252] c8308 unsat8308 (by rfl) a
  have h0 : Entails.eval a c1954 := h 1953 (by decide)
  have h1 : Entails.eval a c2263 := h 2262 (by decide)
  have h2 : Entails.eval a c2241 := h 2240 (by decide)
  have h3 : Entails.eval a c1933 := h 1932 (by decide)
  have h4 : Entails.eval a c2259 := h 2258 (by decide)
  have h5 : Entails.eval a c2252 := h 2251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8309 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c685, some c688, some c691, some c682, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8309 : lratChecker f8309 p8309 = .success := by decide +kernel
theorem unsat8309 : Unsatisfiable (PosFin 65) f8309 := by
  apply lratCheckerSound f8309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8309
  · intro a ha; simp [p8309] at ha; subst a; trivial
  · exact checked8309
theorem derived8309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8309 := by
  apply localUnsat_implies_entails f8309 [c685, c688, c691, c682] c8309 unsat8309 (by rfl) a
  have h0 : Entails.eval a c685 := h 684 (by decide)
  have h1 : Entails.eval a c688 := h 687 (by decide)
  have h2 : Entails.eval a c691 := h 690 (by decide)
  have h3 : Entails.eval a c682 := h 681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8310 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8307, some c8308, some c8309, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8310 : lratChecker f8310 p8310 = .success := by decide +kernel
theorem unsat8310 : Unsatisfiable (PosFin 65) f8310 := by
  apply lratCheckerSound f8310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8310
  · intro a ha; simp [p8310] at ha; subst a; trivial
  · exact checked8310
theorem derived8310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8310 := by
  apply localUnsat_implies_entails f8310 [c8307, c8308, c8309] c8310 unsat8310 (by rfl) a
  have h0 : Entails.eval a c8307 := derived8307 a h
  have h1 : Entails.eval a c8308 := derived8308 a h
  have h2 : Entails.eval a c8309 := derived8309 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8311 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8310, some c8285, some c8286, some c2399, some c2404, some c2373, some c1880, some c2397, some c1605, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8311 : lratChecker f8311 p8311 = .success := by decide +kernel
theorem unsat8311 : Unsatisfiable (PosFin 65) f8311 := by
  apply lratCheckerSound f8311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8311
  · intro a ha; simp [p8311] at ha; subst a; trivial
  · exact checked8311
theorem derived8311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8311 := by
  apply localUnsat_implies_entails f8311 [c8310, c8285, c8286, c2399, c2404, c2373, c1880, c2397, c1605] c8311 unsat8311 (by rfl) a
  have h0 : Entails.eval a c8310 := derived8310 a h
  have h1 : Entails.eval a c8285 := derived8285 a h
  have h2 : Entails.eval a c8286 := derived8286 a h
  have h3 : Entails.eval a c2399 := h 2398 (by decide)
  have h4 : Entails.eval a c2404 := h 2403 (by decide)
  have h5 : Entails.eval a c2373 := h 2372 (by decide)
  have h6 : Entails.eval a c1880 := h 1879 (by decide)
  have h7 : Entails.eval a c2397 := h 2396 (by decide)
  have h8 : Entails.eval a c1605 := h 1604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8312 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2008, some c576, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8312 : lratChecker f8312 p8312 = .success := by decide +kernel
theorem unsat8312 : Unsatisfiable (PosFin 65) f8312 := by
  apply lratCheckerSound f8312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8312
  · intro a ha; simp [p8312] at ha; subst a; trivial
  · exact checked8312
theorem derived8312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8312 := by
  apply localUnsat_implies_entails f8312 [c2008, c576] c8312 unsat8312 (by rfl) a
  have h0 : Entails.eval a c2008 := h 2007 (by decide)
  have h1 : Entails.eval a c576 := h 575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8313 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2522, some c653, some c8295, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8313 : lratChecker f8313 p8313 = .success := by decide +kernel
theorem unsat8313 : Unsatisfiable (PosFin 65) f8313 := by
  apply lratCheckerSound f8313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8313
  · intro a ha; simp [p8313] at ha; subst a; trivial
  · exact checked8313
theorem derived8313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8313 := by
  apply localUnsat_implies_entails f8313 [c2522, c653, c8295] c8313 unsat8313 (by rfl) a
  have h0 : Entails.eval a c2522 := h 2521 (by decide)
  have h1 : Entails.eval a c653 := h 652 (by decide)
  have h2 : Entails.eval a c8295 := derived8295 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8314 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8308, some c8313, some c2404, some c2371, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8314 : lratChecker f8314 p8314 = .success := by decide +kernel
theorem unsat8314 : Unsatisfiable (PosFin 65) f8314 := by
  apply lratCheckerSound f8314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8314
  · intro a ha; simp [p8314] at ha; subst a; trivial
  · exact checked8314
theorem derived8314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8314 := by
  apply localUnsat_implies_entails f8314 [c8308, c8313, c2404, c2371] c8314 unsat8314 (by rfl) a
  have h0 : Entails.eval a c8308 := derived8308 a h
  have h1 : Entails.eval a c8313 := derived8313 a h
  have h2 : Entails.eval a c2404 := h 2403 (by decide)
  have h3 : Entails.eval a c2371 := h 2370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8315 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c668, some c664, some c2534, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8315 : lratChecker f8315 p8315 = .success := by decide +kernel
theorem unsat8315 : Unsatisfiable (PosFin 65) f8315 := by
  apply lratCheckerSound f8315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8315
  · intro a ha; simp [p8315] at ha; subst a; trivial
  · exact checked8315
theorem derived8315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8315 := by
  apply localUnsat_implies_entails f8315 [c668, c664, c2534] c8315 unsat8315 (by rfl) a
  have h0 : Entails.eval a c668 := h 667 (by decide)
  have h1 : Entails.eval a c664 := h 663 (by decide)
  have h2 : Entails.eval a c2534 := h 2533 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8316 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8310, some c8311, some c8308, some c8312, some c8314, some c8315, some c2404, some c2373, some c2403, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8316 : lratChecker f8316 p8316 = .success := by decide +kernel
theorem unsat8316 : Unsatisfiable (PosFin 65) f8316 := by
  apply lratCheckerSound f8316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8316
  · intro a ha; simp [p8316] at ha; subst a; trivial
  · exact checked8316
theorem derived8316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8316 := by
  apply localUnsat_implies_entails f8316 [c8310, c8311, c8308, c8312, c8314, c8315, c2404, c2373, c2403] c8316 unsat8316 (by rfl) a
  have h0 : Entails.eval a c8310 := derived8310 a h
  have h1 : Entails.eval a c8311 := derived8311 a h
  have h2 : Entails.eval a c8308 := derived8308 a h
  have h3 : Entails.eval a c8312 := derived8312 a h
  have h4 : Entails.eval a c8314 := derived8314 a h
  have h5 : Entails.eval a c8315 := derived8315 a h
  have h6 : Entails.eval a c2404 := h 2403 (by decide)
  have h7 : Entails.eval a c2373 := h 2372 (by decide)
  have h8 : Entails.eval a c2403 := h 2402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8317 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c8221, some c8269, some c8280, some c8305, some c8316, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8317 : lratChecker f8317 p8317 = .success := by decide +kernel
theorem unsat8317 : Unsatisfiable (PosFin 65) f8317 := by
  apply lratCheckerSound f8317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8317
  · intro a ha; simp [p8317] at ha; subst a; trivial
  · exact checked8317
theorem derived8317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8317 := by
  apply localUnsat_implies_entails f8317 [c8159, c7849, c8221, c8269, c8280, c8305, c8316] c8317 unsat8317 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8221 := derived8221 a h
  have h3 : Entails.eval a c8269 := derived8269 a h
  have h4 : Entails.eval a c8280 := derived8280 a h
  have h5 : Entails.eval a c8305 := derived8305 a h
  have h6 : Entails.eval a c8316 := derived8316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8318 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8098, some c8224, some c515, some c454, some c864, some c2078, some c2055, some c8172, some c2515, some c2520, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8318 : lratChecker f8318 p8318 = .success := by decide +kernel
theorem unsat8318 : Unsatisfiable (PosFin 65) f8318 := by
  apply lratCheckerSound f8318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8318
  · intro a ha; simp [p8318] at ha; subst a; trivial
  · exact checked8318
theorem derived8318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8318 := by
  apply localUnsat_implies_entails f8318 [c8098, c8224, c515, c454, c864, c2078, c2055, c8172, c2515, c2520] c8318 unsat8318 (by rfl) a
  have h0 : Entails.eval a c8098 := derived8098 a h
  have h1 : Entails.eval a c8224 := derived8224 a h
  have h2 : Entails.eval a c515 := h 514 (by decide)
  have h3 : Entails.eval a c454 := h 453 (by decide)
  have h4 : Entails.eval a c864 := h 863 (by decide)
  have h5 : Entails.eval a c2078 := h 2077 (by decide)
  have h6 : Entails.eval a c2055 := h 2054 (by decide)
  have h7 : Entails.eval a c8172 := derived8172 a h
  have h8 : Entails.eval a c2515 := h 2514 (by decide)
  have h9 : Entails.eval a c2520 := h 2519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8319 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c454, some c434, some c435, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8319 : lratChecker f8319 p8319 = .success := by decide +kernel
theorem unsat8319 : Unsatisfiable (PosFin 65) f8319 := by
  apply lratCheckerSound f8319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8319
  · intro a ha; simp [p8319] at ha; subst a; trivial
  · exact checked8319
theorem derived8319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8319 := by
  apply localUnsat_implies_entails f8319 [c454, c434, c435] c8319 unsat8319 (by rfl) a
  have h0 : Entails.eval a c454 := h 453 (by decide)
  have h1 : Entails.eval a c434 := h 433 (by decide)
  have h2 : Entails.eval a c435 := h 434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8320 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8319, some c8098, some c8318, some c1988, some c1984, some c515, some c2009, some c2169, some c2144, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8320 : lratChecker f8320 p8320 = .success := by decide +kernel
theorem unsat8320 : Unsatisfiable (PosFin 65) f8320 := by
  apply lratCheckerSound f8320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8320
  · intro a ha; simp [p8320] at ha; subst a; trivial
  · exact checked8320
theorem derived8320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8320 := by
  apply localUnsat_implies_entails f8320 [c8319, c8098, c8318, c1988, c1984, c515, c2009, c2169, c2144] c8320 unsat8320 (by rfl) a
  have h0 : Entails.eval a c8319 := derived8319 a h
  have h1 : Entails.eval a c8098 := derived8098 a h
  have h2 : Entails.eval a c8318 := derived8318 a h
  have h3 : Entails.eval a c1988 := h 1987 (by decide)
  have h4 : Entails.eval a c1984 := h 1983 (by decide)
  have h5 : Entails.eval a c515 := h 514 (by decide)
  have h6 : Entails.eval a c2009 := h 2008 (by decide)
  have h7 : Entails.eval a c2169 := h 2168 (by decide)
  have h8 : Entails.eval a c2144 := h 2143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8321 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8098, some c8319, some c8320, some c1926, some c1896, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8321 : lratChecker f8321 p8321 = .success := by decide +kernel
theorem unsat8321 : Unsatisfiable (PosFin 65) f8321 := by
  apply lratCheckerSound f8321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8321
  · intro a ha; simp [p8321] at ha; subst a; trivial
  · exact checked8321
theorem derived8321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8321 := by
  apply localUnsat_implies_entails f8321 [c8098, c8319, c8320, c1926, c1896] c8321 unsat8321 (by rfl) a
  have h0 : Entails.eval a c8098 := derived8098 a h
  have h1 : Entails.eval a c8319 := derived8319 a h
  have h2 : Entails.eval a c8320 := derived8320 a h
  have h3 : Entails.eval a c1926 := h 1925 (by decide)
  have h4 : Entails.eval a c1896 := h 1895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8322 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8321, some c8256, some c1568, some c499, some c1823, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8322 : lratChecker f8322 p8322 = .success := by decide +kernel
theorem unsat8322 : Unsatisfiable (PosFin 65) f8322 := by
  apply lratCheckerSound f8322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8322
  · intro a ha; simp [p8322] at ha; subst a; trivial
  · exact checked8322
theorem derived8322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8322 := by
  apply localUnsat_implies_entails f8322 [c8321, c8256, c1568, c499, c1823] c8322 unsat8322 (by rfl) a
  have h0 : Entails.eval a c8321 := derived8321 a h
  have h1 : Entails.eval a c8256 := derived8256 a h
  have h2 : Entails.eval a c1568 := h 1567 (by decide)
  have h3 : Entails.eval a c499 := h 498 (by decide)
  have h4 : Entails.eval a c1823 := h 1822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8323 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1020, some c1571, some c2083, some c955, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8323 : lratChecker f8323 p8323 = .success := by decide +kernel
theorem unsat8323 : Unsatisfiable (PosFin 65) f8323 := by
  apply lratCheckerSound f8323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8323
  · intro a ha; simp [p8323] at ha; subst a; trivial
  · exact checked8323
theorem derived8323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8323 := by
  apply localUnsat_implies_entails f8323 [c1020, c1571, c2083, c955] c8323 unsat8323 (by rfl) a
  have h0 : Entails.eval a c1020 := h 1019 (by decide)
  have h1 : Entails.eval a c1571 := h 1570 (by decide)
  have h2 : Entails.eval a c2083 := h 2082 (by decide)
  have h3 : Entails.eval a c955 := h 954 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8324 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8322, some c8321, some c8323, some c8103, some c7961, some c8116, some c504, some c2571, some c683, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8324 : lratChecker f8324 p8324 = .success := by decide +kernel
theorem unsat8324 : Unsatisfiable (PosFin 65) f8324 := by
  apply lratCheckerSound f8324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8324
  · intro a ha; simp [p8324] at ha; subst a; trivial
  · exact checked8324
theorem derived8324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8324 := by
  apply localUnsat_implies_entails f8324 [c8322, c8321, c8323, c8103, c7961, c8116, c504, c2571, c683] c8324 unsat8324 (by rfl) a
  have h0 : Entails.eval a c8322 := derived8322 a h
  have h1 : Entails.eval a c8321 := derived8321 a h
  have h2 : Entails.eval a c8323 := derived8323 a h
  have h3 : Entails.eval a c8103 := derived8103 a h
  have h4 : Entails.eval a c7961 := derived7961 a h
  have h5 : Entails.eval a c8116 := derived8116 a h
  have h6 : Entails.eval a c504 := h 503 (by decide)
  have h7 : Entails.eval a c2571 := h 2570 (by decide)
  have h8 : Entails.eval a c683 := h 682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8325 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8317, some c8321, some c8159, some c8324, some c8240, some c515, some c1608, some c1828, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8325 : lratChecker f8325 p8325 = .success := by decide +kernel
theorem unsat8325 : Unsatisfiable (PosFin 65) f8325 := by
  apply lratCheckerSound f8325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8325
  · intro a ha; simp [p8325] at ha; subst a; trivial
  · exact checked8325
theorem derived8325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8325 := by
  apply localUnsat_implies_entails f8325 [c7849, c8317, c8321, c8159, c8324, c8240, c515, c1608, c1828] c8325 unsat8325 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c8324 := derived8324 a h
  have h5 : Entails.eval a c8240 := derived8240 a h
  have h6 : Entails.eval a c515 := h 514 (by decide)
  have h7 : Entails.eval a c1608 := h 1607 (by decide)
  have h8 : Entails.eval a c1828 := h 1827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8326 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2274, some c528, some c2076, some c499, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8326 : lratChecker f8326 p8326 = .success := by decide +kernel
theorem unsat8326 : Unsatisfiable (PosFin 65) f8326 := by
  apply lratCheckerSound f8326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8326
  · intro a ha; simp [p8326] at ha; subst a; trivial
  · exact checked8326
theorem derived8326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8326 := by
  apply localUnsat_implies_entails f8326 [c2274, c528, c2076, c499] c8326 unsat8326 (by rfl) a
  have h0 : Entails.eval a c2274 := h 2273 (by decide)
  have h1 : Entails.eval a c528 := h 527 (by decide)
  have h2 : Entails.eval a c2076 := h 2075 (by decide)
  have h3 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8327 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8321, some c8326, some c8103, some c7961, some c8116, some c504, some c2571, some c1828, some c1749, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8327 : lratChecker f8327 p8327 = .success := by decide +kernel
theorem unsat8327 : Unsatisfiable (PosFin 65) f8327 := by
  apply lratCheckerSound f8327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8327
  · intro a ha; simp [p8327] at ha; subst a; trivial
  · exact checked8327
theorem derived8327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8327 := by
  apply localUnsat_implies_entails f8327 [c8321, c8326, c8103, c7961, c8116, c504, c2571, c1828, c1749] c8327 unsat8327 (by rfl) a
  have h0 : Entails.eval a c8321 := derived8321 a h
  have h1 : Entails.eval a c8326 := derived8326 a h
  have h2 : Entails.eval a c8103 := derived8103 a h
  have h3 : Entails.eval a c7961 := derived7961 a h
  have h4 : Entails.eval a c8116 := derived8116 a h
  have h5 : Entails.eval a c504 := h 503 (by decide)
  have h6 : Entails.eval a c2571 := h 2570 (by decide)
  have h7 : Entails.eval a c1828 := h 1827 (by decide)
  have h8 : Entails.eval a c1749 := h 1748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8328 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8317, some c8321, some c8159, some c8325, some c8327, some c8240, some c515, some c1828, some c2578, some c1751, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8328 : lratChecker f8328 p8328 = .success := by decide +kernel
theorem unsat8328 : Unsatisfiable (PosFin 65) f8328 := by
  apply lratCheckerSound f8328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8328
  · intro a ha; simp [p8328] at ha; subst a; trivial
  · exact checked8328
theorem derived8328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8328 := by
  apply localUnsat_implies_entails f8328 [c7849, c8317, c8321, c8159, c8325, c8327, c8240, c515, c1828, c2578, c1751] c8328 unsat8328 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c8325 := derived8325 a h
  have h5 : Entails.eval a c8327 := derived8327 a h
  have h6 : Entails.eval a c8240 := derived8240 a h
  have h7 : Entails.eval a c515 := h 514 (by decide)
  have h8 : Entails.eval a c1828 := h 1827 (by decide)
  have h9 : Entails.eval a c2578 := h 2577 (by decide)
  have h10 : Entails.eval a c1751 := h 1750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8329 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8256, some c2081, some c2386, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8329 : lratChecker f8329 p8329 = .success := by decide +kernel
theorem unsat8329 : Unsatisfiable (PosFin 65) f8329 := by
  apply lratCheckerSound f8329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8329
  · intro a ha; simp [p8329] at ha; subst a; trivial
  · exact checked8329
theorem derived8329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8329 := by
  apply localUnsat_implies_entails f8329 [c8256, c2081, c2386] c8329 unsat8329 (by rfl) a
  have h0 : Entails.eval a c8256 := derived8256 a h
  have h1 : Entails.eval a c2081 := h 2080 (by decide)
  have h2 : Entails.eval a c2386 := h 2385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8330 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8321, some c2247, some c8247, some c657, some c2386, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8330 : lratChecker f8330 p8330 = .success := by decide +kernel
theorem unsat8330 : Unsatisfiable (PosFin 65) f8330 := by
  apply lratCheckerSound f8330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8330
  · intro a ha; simp [p8330] at ha; subst a; trivial
  · exact checked8330
theorem derived8330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8330 := by
  apply localUnsat_implies_entails f8330 [c8321, c2247, c8247, c657, c2386] c8330 unsat8330 (by rfl) a
  have h0 : Entails.eval a c8321 := derived8321 a h
  have h1 : Entails.eval a c2247 := h 2246 (by decide)
  have h2 : Entails.eval a c8247 := derived8247 a h
  have h3 : Entails.eval a c657 := h 656 (by decide)
  have h4 : Entails.eval a c2386 := h 2385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8331 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8321, some c8330, some c2265, some c693, some c683, some c686, some c689, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8331 : lratChecker f8331 p8331 = .success := by decide +kernel
theorem unsat8331 : Unsatisfiable (PosFin 65) f8331 := by
  apply lratCheckerSound f8331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8331
  · intro a ha; simp [p8331] at ha; subst a; trivial
  · exact checked8331
theorem derived8331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8331 := by
  apply localUnsat_implies_entails f8331 [c8321, c8330, c2265, c693, c683, c686, c689] c8331 unsat8331 (by rfl) a
  have h0 : Entails.eval a c8321 := derived8321 a h
  have h1 : Entails.eval a c8330 := derived8330 a h
  have h2 : Entails.eval a c2265 := h 2264 (by decide)
  have h3 : Entails.eval a c693 := h 692 (by decide)
  have h4 : Entails.eval a c683 := h 682 (by decide)
  have h5 : Entails.eval a c686 := h 685 (by decide)
  have h6 : Entails.eval a c689 := h 688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8332 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c467, some c2083, some c2647, some c456, some c2506, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8332 : lratChecker f8332 p8332 = .success := by decide +kernel
theorem unsat8332 : Unsatisfiable (PosFin 65) f8332 := by
  apply lratCheckerSound f8332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8332
  · intro a ha; simp [p8332] at ha; subst a; trivial
  · exact checked8332
theorem derived8332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8332 := by
  apply localUnsat_implies_entails f8332 [c467, c2083, c2647, c456, c2506] c8332 unsat8332 (by rfl) a
  have h0 : Entails.eval a c467 := h 466 (by decide)
  have h1 : Entails.eval a c2083 := h 2082 (by decide)
  have h2 : Entails.eval a c2647 := h 2646 (by decide)
  have h3 : Entails.eval a c456 := h 455 (by decide)
  have h4 : Entails.eval a c2506 := h 2505 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8333 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨13, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8321, some c8329, some c8331, some c8332, some c1204, some c1208, some c2369, some c1870, some c2376, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8333 : lratChecker f8333 p8333 = .success := by decide +kernel
theorem unsat8333 : Unsatisfiable (PosFin 65) f8333 := by
  apply lratCheckerSound f8333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8333
  · intro a ha; simp [p8333] at ha; subst a; trivial
  · exact checked8333
theorem derived8333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8333 := by
  apply localUnsat_implies_entails f8333 [c8321, c8329, c8331, c8332, c1204, c1208, c2369, c1870, c2376] c8333 unsat8333 (by rfl) a
  have h0 : Entails.eval a c8321 := derived8321 a h
  have h1 : Entails.eval a c8329 := derived8329 a h
  have h2 : Entails.eval a c8331 := derived8331 a h
  have h3 : Entails.eval a c8332 := derived8332 a h
  have h4 : Entails.eval a c1204 := h 1203 (by decide)
  have h5 : Entails.eval a c1208 := h 1207 (by decide)
  have h6 : Entails.eval a c2369 := h 2368 (by decide)
  have h7 : Entails.eval a c1870 := h 1869 (by decide)
  have h8 : Entails.eval a c2376 := h 2375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8334 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8159, some c8317, some c8328, some c8321, some c8329, some c8331, some c8240, some c1608, some c2265, some c986, some c948, some c1252, some c1297, some c581, some c1040, some c8333, some c467, some c2083, some c2647, some c476, some c466, some c1454, some c2644, some c822, some c7783, some c27, some c455, some c45, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked8334 : lratChecker f8334 p8334 = .success := by decide +kernel
theorem unsat8334 : Unsatisfiable (PosFin 65) f8334 := by
  apply lratCheckerSound f8334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8334
  · intro a ha; simp [p8334] at ha; subst a; trivial
  · exact checked8334
theorem derived8334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8334 := by
  apply localUnsat_implies_entails f8334 [c7849, c8159, c8317, c8328, c8321, c8329, c8331, c8240, c1608, c2265, c986, c948, c1252, c1297, c581, c1040, c8333, c467, c2083, c2647, c476, c466, c1454, c2644, c822, c7783, c27, c455, c45] c8334 unsat8334 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c8317 := derived8317 a h
  have h3 : Entails.eval a c8328 := derived8328 a h
  have h4 : Entails.eval a c8321 := derived8321 a h
  have h5 : Entails.eval a c8329 := derived8329 a h
  have h6 : Entails.eval a c8331 := derived8331 a h
  have h7 : Entails.eval a c8240 := derived8240 a h
  have h8 : Entails.eval a c1608 := h 1607 (by decide)
  have h9 : Entails.eval a c2265 := h 2264 (by decide)
  have h10 : Entails.eval a c986 := h 985 (by decide)
  have h11 : Entails.eval a c948 := h 947 (by decide)
  have h12 : Entails.eval a c1252 := h 1251 (by decide)
  have h13 : Entails.eval a c1297 := h 1296 (by decide)
  have h14 : Entails.eval a c581 := h 580 (by decide)
  have h15 : Entails.eval a c1040 := h 1039 (by decide)
  have h16 : Entails.eval a c8333 := derived8333 a h
  have h17 : Entails.eval a c467 := h 466 (by decide)
  have h18 : Entails.eval a c2083 := h 2082 (by decide)
  have h19 : Entails.eval a c2647 := h 2646 (by decide)
  have h20 : Entails.eval a c476 := h 475 (by decide)
  have h21 : Entails.eval a c466 := h 465 (by decide)
  have h22 : Entails.eval a c1454 := h 1453 (by decide)
  have h23 : Entails.eval a c2644 := h 2643 (by decide)
  have h24 : Entails.eval a c822 := h 821 (by decide)
  have h25 : Entails.eval a c7783 := derived7783 a h
  have h26 : Entails.eval a c27 := h 26 (by decide)
  have h27 : Entails.eval a c455 := h 454 (by decide)
  have h28 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8335 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8328, some c7849, some c8317, some c8321, some c8159, some c8329, some c8331, some c8240, some c1608, some c2265, some c986, some c948, some c1252, some c581, some c1297, some c1040, some c8333, some c8334, some c1204, some c1208, some c959, some c1867, some c962, some c1206, some c1870, some c7783, some c48, some c45, some c27, some c2225, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked8335 : lratChecker f8335 p8335 = .success := by decide +kernel
theorem unsat8335 : Unsatisfiable (PosFin 65) f8335 := by
  apply lratCheckerSound f8335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8335
  · intro a ha; simp [p8335] at ha; subst a; trivial
  · exact checked8335
theorem derived8335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8335 := by
  apply localUnsat_implies_entails f8335 [c8328, c7849, c8317, c8321, c8159, c8329, c8331, c8240, c1608, c2265, c986, c948, c1252, c581, c1297, c1040, c8333, c8334, c1204, c1208, c959, c1867, c962, c1206, c1870, c7783, c48, c45, c27, c2225] c8335 unsat8335 (by rfl) a
  have h0 : Entails.eval a c8328 := derived8328 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8317 := derived8317 a h
  have h3 : Entails.eval a c8321 := derived8321 a h
  have h4 : Entails.eval a c8159 := derived8159 a h
  have h5 : Entails.eval a c8329 := derived8329 a h
  have h6 : Entails.eval a c8331 := derived8331 a h
  have h7 : Entails.eval a c8240 := derived8240 a h
  have h8 : Entails.eval a c1608 := h 1607 (by decide)
  have h9 : Entails.eval a c2265 := h 2264 (by decide)
  have h10 : Entails.eval a c986 := h 985 (by decide)
  have h11 : Entails.eval a c948 := h 947 (by decide)
  have h12 : Entails.eval a c1252 := h 1251 (by decide)
  have h13 : Entails.eval a c581 := h 580 (by decide)
  have h14 : Entails.eval a c1297 := h 1296 (by decide)
  have h15 : Entails.eval a c1040 := h 1039 (by decide)
  have h16 : Entails.eval a c8333 := derived8333 a h
  have h17 : Entails.eval a c8334 := derived8334 a h
  have h18 : Entails.eval a c1204 := h 1203 (by decide)
  have h19 : Entails.eval a c1208 := h 1207 (by decide)
  have h20 : Entails.eval a c959 := h 958 (by decide)
  have h21 : Entails.eval a c1867 := h 1866 (by decide)
  have h22 : Entails.eval a c962 := h 961 (by decide)
  have h23 : Entails.eval a c1206 := h 1205 (by decide)
  have h24 : Entails.eval a c1870 := h 1869 (by decide)
  have h25 : Entails.eval a c7783 := derived7783 a h
  have h26 : Entails.eval a c48 := h 47 (by decide)
  have h27 : Entails.eval a c45 := h 44 (by decide)
  have h28 : Entails.eval a c27 := h 26 (by decide)
  have h29 : Entails.eval a c2225 := h 2224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8336 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2265, some c1926, some c581, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8336 : lratChecker f8336 p8336 = .success := by decide +kernel
theorem unsat8336 : Unsatisfiable (PosFin 65) f8336 := by
  apply lratCheckerSound f8336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8336
  · intro a ha; simp [p8336] at ha; subst a; trivial
  · exact checked8336
theorem derived8336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8336 := by
  apply localUnsat_implies_entails f8336 [c2265, c1926, c581] c8336 unsat8336 (by rfl) a
  have h0 : Entails.eval a c2265 := h 2264 (by decide)
  have h1 : Entails.eval a c1926 := h 1925 (by decide)
  have h2 : Entails.eval a c581 := h 580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8337 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8317, some c7849, some c8321, some c8328, some c8335, some c8336, some c8240, some c8275, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8337 : lratChecker f8337 p8337 = .success := by decide +kernel
theorem unsat8337 : Unsatisfiable (PosFin 65) f8337 := by
  apply lratCheckerSound f8337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8337
  · intro a ha; simp [p8337] at ha; subst a; trivial
  · exact checked8337
theorem derived8337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8337 := by
  apply localUnsat_implies_entails f8337 [c8317, c7849, c8321, c8328, c8335, c8336, c8240, c8275] c8337 unsat8337 (by rfl) a
  have h0 : Entails.eval a c8317 := derived8317 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8321 := derived8321 a h
  have h3 : Entails.eval a c8328 := derived8328 a h
  have h4 : Entails.eval a c8335 := derived8335 a h
  have h5 : Entails.eval a c8336 := derived8336 a h
  have h6 : Entails.eval a c8240 := derived8240 a h
  have h7 : Entails.eval a c8275 := derived8275 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8338 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8337, some c8317, some c8159, some c7849, some c8098, some c8319, some c8111, some c1987, some c8261, some c1983, some c1999, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8338 : lratChecker f8338 p8338 = .success := by decide +kernel
theorem unsat8338 : Unsatisfiable (PosFin 65) f8338 := by
  apply lratCheckerSound f8338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8338
  · intro a ha; simp [p8338] at ha; subst a; trivial
  · exact checked8338
theorem derived8338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8338 := by
  apply localUnsat_implies_entails f8338 [c8337, c8317, c8159, c7849, c8098, c8319, c8111, c1987, c8261, c1983, c1999] c8338 unsat8338 (by rfl) a
  have h0 : Entails.eval a c8337 := derived8337 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8098 := derived8098 a h
  have h5 : Entails.eval a c8319 := derived8319 a h
  have h6 : Entails.eval a c8111 := derived8111 a h
  have h7 : Entails.eval a c1987 := h 1986 (by decide)
  have h8 : Entails.eval a c8261 := derived8261 a h
  have h9 : Entails.eval a c1983 := h 1982 (by decide)
  have h10 : Entails.eval a c1999 := h 1998 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8339 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c515, some c1608, some c1828, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8339 : lratChecker f8339 p8339 = .success := by decide +kernel
theorem unsat8339 : Unsatisfiable (PosFin 65) f8339 := by
  apply lratCheckerSound f8339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8339
  · intro a ha; simp [p8339] at ha; subst a; trivial
  · exact checked8339
theorem derived8339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8339 := by
  apply localUnsat_implies_entails f8339 [c515, c1608, c1828] c8339 unsat8339 (by rfl) a
  have h0 : Entails.eval a c515 := h 514 (by decide)
  have h1 : Entails.eval a c1608 := h 1607 (by decide)
  have h2 : Entails.eval a c1828 := h 1827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8340 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8338, some c8337, some c8317, some c8159, some c7849, some c8339, some c8245, some c8253, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8340 : lratChecker f8340 p8340 = .success := by decide +kernel
theorem unsat8340 : Unsatisfiable (PosFin 65) f8340 := by
  apply lratCheckerSound f8340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8340
  · intro a ha; simp [p8340] at ha; subst a; trivial
  · exact checked8340
theorem derived8340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8340 := by
  apply localUnsat_implies_entails f8340 [c8338, c8337, c8317, c8159, c7849, c8339, c8245, c8253] c8340 unsat8340 (by rfl) a
  have h0 : Entails.eval a c8338 := derived8338 a h
  have h1 : Entails.eval a c8337 := derived8337 a h
  have h2 : Entails.eval a c8317 := derived8317 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c7849 := derived7849 a h
  have h5 : Entails.eval a c8339 := derived8339 a h
  have h6 : Entails.eval a c8245 := derived8245 a h
  have h7 : Entails.eval a c8253 := derived8253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8341 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c515, some c1828, some c2578, some c1751, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8341 : lratChecker f8341 p8341 = .success := by decide +kernel
theorem unsat8341 : Unsatisfiable (PosFin 65) f8341 := by
  apply lratCheckerSound f8341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8341
  · intro a ha; simp [p8341] at ha; subst a; trivial
  · exact checked8341
theorem derived8341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8341 := by
  apply localUnsat_implies_entails f8341 [c515, c1828, c2578, c1751] c8341 unsat8341 (by rfl) a
  have h0 : Entails.eval a c515 := h 514 (by decide)
  have h1 : Entails.eval a c1828 := h 1827 (by decide)
  have h2 : Entails.eval a c2578 := h 2577 (by decide)
  have h3 : Entails.eval a c1751 := h 1750 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8342 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c499, some c497, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8342 : lratChecker f8342 p8342 = .success := by decide +kernel
theorem unsat8342 : Unsatisfiable (PosFin 65) f8342 := by
  apply lratCheckerSound f8342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8342
  · intro a ha; simp [p8342] at ha; subst a; trivial
  · exact checked8342
theorem derived8342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8342 := by
  apply localUnsat_implies_entails f8342 [c499, c497] c8342 unsat8342 (by rfl) a
  have h0 : Entails.eval a c499 := h 498 (by decide)
  have h1 : Entails.eval a c497 := h 496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8343 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8337, some c8317, some c8159, some c7849, some c8338, some c8340, some c8341, some c8245, some c8261, some c8342, some c2142, some c2163, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8343 : lratChecker f8343 p8343 = .success := by decide +kernel
theorem unsat8343 : Unsatisfiable (PosFin 65) f8343 := by
  apply lratCheckerSound f8343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8343
  · intro a ha; simp [p8343] at ha; subst a; trivial
  · exact checked8343
theorem derived8343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8343 := by
  apply localUnsat_implies_entails f8343 [c8337, c8317, c8159, c7849, c8338, c8340, c8341, c8245, c8261, c8342, c2142, c2163] c8343 unsat8343 (by rfl) a
  have h0 : Entails.eval a c8337 := derived8337 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8338 := derived8338 a h
  have h5 : Entails.eval a c8340 := derived8340 a h
  have h6 : Entails.eval a c8341 := derived8341 a h
  have h7 : Entails.eval a c8245 := derived8245 a h
  have h8 : Entails.eval a c8261 := derived8261 a h
  have h9 : Entails.eval a c8342 := derived8342 a h
  have h10 : Entails.eval a c2142 := h 2141 (by decide)
  have h11 : Entails.eval a c2163 := h 2162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8344 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8098, some c8319, some c8196, some c8203, some c1895, some c1926, some c1910, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8344 : lratChecker f8344 p8344 = .success := by decide +kernel
theorem unsat8344 : Unsatisfiable (PosFin 65) f8344 := by
  apply lratCheckerSound f8344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8344
  · intro a ha; simp [p8344] at ha; subst a; trivial
  · exact checked8344
theorem derived8344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8344 := by
  apply localUnsat_implies_entails f8344 [c8098, c8319, c8196, c8203, c1895, c1926, c1910] c8344 unsat8344 (by rfl) a
  have h0 : Entails.eval a c8098 := derived8098 a h
  have h1 : Entails.eval a c8319 := derived8319 a h
  have h2 : Entails.eval a c8196 := derived8196 a h
  have h3 : Entails.eval a c8203 := derived8203 a h
  have h4 : Entails.eval a c1895 := h 1894 (by decide)
  have h5 : Entails.eval a c1926 := h 1925 (by decide)
  have h6 : Entails.eval a c1910 := h 1909 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8345 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2086, some c466, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8345 : lratChecker f8345 p8345 = .success := by decide +kernel
theorem unsat8345 : Unsatisfiable (PosFin 65) f8345 := by
  apply lratCheckerSound f8345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8345
  · intro a ha; simp [p8345] at ha; subst a; trivial
  · exact checked8345
theorem derived8345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8345 := by
  apply localUnsat_implies_entails f8345 [c2086, c466] c8345 unsat8345 (by rfl) a
  have h0 : Entails.eval a c2086 := h 2085 (by decide)
  have h1 : Entails.eval a c466 := h 465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8346 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8248, some c8265, some c8345, some c2374, some c2384, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8346 : lratChecker f8346 p8346 = .success := by decide +kernel
theorem unsat8346 : Unsatisfiable (PosFin 65) f8346 := by
  apply lratCheckerSound f8346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8346
  · intro a ha; simp [p8346] at ha; subst a; trivial
  · exact checked8346
theorem derived8346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8346 := by
  apply localUnsat_implies_entails f8346 [c8248, c8265, c8345, c2374, c2384] c8346 unsat8346 (by rfl) a
  have h0 : Entails.eval a c8248 := derived8248 a h
  have h1 : Entails.eval a c8265 := derived8265 a h
  have h2 : Entails.eval a c8345 := derived8345 a h
  have h3 : Entails.eval a c2374 := h 2373 (by decide)
  have h4 : Entails.eval a c2384 := h 2383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8347 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8344, some c8248, some c8346, some c8336, some c8247, some c2255, some c8268, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8347 : lratChecker f8347 p8347 = .success := by decide +kernel
theorem unsat8347 : Unsatisfiable (PosFin 65) f8347 := by
  apply lratCheckerSound f8347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8347
  · intro a ha; simp [p8347] at ha; subst a; trivial
  · exact checked8347
theorem derived8347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8347 := by
  apply localUnsat_implies_entails f8347 [c8344, c8248, c8346, c8336, c8247, c2255, c8268] c8347 unsat8347 (by rfl) a
  have h0 : Entails.eval a c8344 := derived8344 a h
  have h1 : Entails.eval a c8248 := derived8248 a h
  have h2 : Entails.eval a c8346 := derived8346 a h
  have h3 : Entails.eval a c8336 := derived8336 a h
  have h4 : Entails.eval a c8247 := derived8247 a h
  have h5 : Entails.eval a c2255 := h 2254 (by decide)
  have h6 : Entails.eval a c8268 := derived8268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8348 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8317, some c8159, some c7849, some c8337, some c8343, some c8347, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8348 : lratChecker f8348 p8348 = .success := by decide +kernel
theorem unsat8348 : Unsatisfiable (PosFin 65) f8348 := by
  apply lratCheckerSound f8348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8348
  · intro a ha; simp [p8348] at ha; subst a; trivial
  · exact checked8348
theorem derived8348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8348 := by
  apply localUnsat_implies_entails f8348 [c8317, c8159, c7849, c8337, c8343, c8347] c8348 unsat8348 (by rfl) a
  have h0 : Entails.eval a c8317 := derived8317 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c8337 := derived8337 a h
  have h4 : Entails.eval a c8343 := derived8343 a h
  have h5 : Entails.eval a c8347 := derived8347 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8349 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8214, some c8124, some c8134, some c1988, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8349 : lratChecker f8349 p8349 = .success := by decide +kernel
theorem unsat8349 : Unsatisfiable (PosFin 65) f8349 := by
  apply lratCheckerSound f8349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8349
  · intro a ha; simp [p8349] at ha; subst a; trivial
  · exact checked8349
theorem derived8349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8349 := by
  apply localUnsat_implies_entails f8349 [c8217, c8214, c8124, c8134, c1988] c8349 unsat8349 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8214 := derived8214 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8134 := derived8134 a h
  have h4 : Entails.eval a c1988 := h 1987 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8350 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8217, some c8214, some c8349, some c8302, some c508, some c504, some c501, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8350 : lratChecker f8350 p8350 = .success := by decide +kernel
theorem unsat8350 : Unsatisfiable (PosFin 65) f8350 := by
  apply lratCheckerSound f8350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8350
  · intro a ha; simp [p8350] at ha; subst a; trivial
  · exact checked8350
theorem derived8350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8350 := by
  apply localUnsat_implies_entails f8350 [c8124, c8217, c8214, c8349, c8302, c508, c504, c501] c8350 unsat8350 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8217 := derived8217 a h
  have h2 : Entails.eval a c8214 := derived8214 a h
  have h3 : Entails.eval a c8349 := derived8349 a h
  have h4 : Entails.eval a c8302 := derived8302 a h
  have h5 : Entails.eval a c508 := h 507 (by decide)
  have h6 : Entails.eval a c504 := h 503 (by decide)
  have h7 : Entails.eval a c501 := h 500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8351 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c8309, some c507, some c2576, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8351 : lratChecker f8351 p8351 = .success := by decide +kernel
theorem unsat8351 : Unsatisfiable (PosFin 65) f8351 := by
  apply lratCheckerSound f8351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8351
  · intro a ha; simp [p8351] at ha; subst a; trivial
  · exact checked8351
theorem derived8351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8351 := by
  apply localUnsat_implies_entails f8351 [c545, c553, c8309, c507, c2576] c8351 unsat8351 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c8309 := derived8309 a h
  have h3 : Entails.eval a c507 := h 506 (by decide)
  have h4 : Entails.eval a c2576 := h 2575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8352 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8285, some c8292, some c8286, some c1886, some c1868, some c1880, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8352 : lratChecker f8352 p8352 = .success := by decide +kernel
theorem unsat8352 : Unsatisfiable (PosFin 65) f8352 := by
  apply lratCheckerSound f8352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8352
  · intro a ha; simp [p8352] at ha; subst a; trivial
  · exact checked8352
theorem derived8352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8352 := by
  apply localUnsat_implies_entails f8352 [c8285, c8292, c8286, c1886, c1868, c1880] c8352 unsat8352 (by rfl) a
  have h0 : Entails.eval a c8285 := derived8285 a h
  have h1 : Entails.eval a c8292 := derived8292 a h
  have h2 : Entails.eval a c8286 := derived8286 a h
  have h3 : Entails.eval a c1886 := h 1885 (by decide)
  have h4 : Entails.eval a c1868 := h 1867 (by decide)
  have h5 : Entails.eval a c1880 := h 1879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8353 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c508, some c504, some c501, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8353 : lratChecker f8353 p8353 = .success := by decide +kernel
theorem unsat8353 : Unsatisfiable (PosFin 65) f8353 := by
  apply lratCheckerSound f8353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8353
  · intro a ha; simp [p8353] at ha; subst a; trivial
  · exact checked8353
theorem derived8353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8353 := by
  apply localUnsat_implies_entails f8353 [c508, c504, c501] c8353 unsat8353 (by rfl) a
  have h0 : Entails.eval a c508 := h 507 (by decide)
  have h1 : Entails.eval a c504 := h 503 (by decide)
  have h2 : Entails.eval a c501 := h 500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8354 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8302, some c2152, some c2164, some c2151, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p8354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8354 : lratChecker f8354 p8354 = .success := by decide +kernel
theorem unsat8354 : Unsatisfiable (PosFin 65) f8354 := by
  apply lratCheckerSound f8354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8354
  · intro a ha; simp [p8354] at ha; subst a; trivial
  · exact checked8354
theorem derived8354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8354 := by
  apply localUnsat_implies_entails f8354 [c8302, c2152, c2164, c2151] c8354 unsat8354 (by rfl) a
  have h0 : Entails.eval a c8302 := derived8302 a h
  have h1 : Entails.eval a c2152 := h 2151 (by decide)
  have h2 : Entails.eval a c2164 := h 2163 (by decide)
  have h3 : Entails.eval a c2151 := h 2150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8355 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8348, some c8317, some c8159, some c7849, some c8350, some c8351, some c8240, some c8352, some c8353, some c8354, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8355 : lratChecker f8355 p8355 = .success := by decide +kernel
theorem unsat8355 : Unsatisfiable (PosFin 65) f8355 := by
  apply lratCheckerSound f8355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8355
  · intro a ha; simp [p8355] at ha; subst a; trivial
  · exact checked8355
theorem derived8355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8355 := by
  apply localUnsat_implies_entails f8355 [c8348, c8317, c8159, c7849, c8350, c8351, c8240, c8352, c8353, c8354] c8355 unsat8355 (by rfl) a
  have h0 : Entails.eval a c8348 := derived8348 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8350 := derived8350 a h
  have h5 : Entails.eval a c8351 := derived8351 a h
  have h6 : Entails.eval a c8240 := derived8240 a h
  have h7 : Entails.eval a c8352 := derived8352 a h
  have h8 : Entails.eval a c8353 := derived8353 a h
  have h9 : Entails.eval a c8354 := derived8354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8356 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2013, some c1911, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8356 : lratChecker f8356 p8356 = .success := by decide +kernel
theorem unsat8356 : Unsatisfiable (PosFin 65) f8356 := by
  apply lratCheckerSound f8356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8356
  · intro a ha; simp [p8356] at ha; subst a; trivial
  · exact checked8356
theorem derived8356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8356 := by
  apply localUnsat_implies_entails f8356 [c2013, c1911] c8356 unsat8356 (by rfl) a
  have h0 : Entails.eval a c2013 := h 2012 (by decide)
  have h1 : Entails.eval a c1911 := h 1910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8357 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8217, some c8214, some c8124, some c8356, some c642, some c624, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8357 : lratChecker f8357 p8357 = .success := by decide +kernel
theorem unsat8357 : Unsatisfiable (PosFin 65) f8357 := by
  apply lratCheckerSound f8357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8357
  · intro a ha; simp [p8357] at ha; subst a; trivial
  · exact checked8357
theorem derived8357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8357 := by
  apply localUnsat_implies_entails f8357 [c8217, c8214, c8124, c8356, c642, c624] c8357 unsat8357 (by rfl) a
  have h0 : Entails.eval a c8217 := derived8217 a h
  have h1 : Entails.eval a c8214 := derived8214 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8356 := derived8356 a h
  have h4 : Entails.eval a c642 := h 641 (by decide)
  have h5 : Entails.eval a c624 := h 623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8358 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨31, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2122, some c2634, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8358 : lratChecker f8358 p8358 = .success := by decide +kernel
theorem unsat8358 : Unsatisfiable (PosFin 65) f8358 := by
  apply lratCheckerSound f8358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8358
  · intro a ha; simp [p8358] at ha; subst a; trivial
  · exact checked8358
theorem derived8358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8358 := by
  apply localUnsat_implies_entails f8358 [c2122, c2634] c8358 unsat8358 (by rfl) a
  have h0 : Entails.eval a c2122 := h 2121 (by decide)
  have h1 : Entails.eval a c2634 := h 2633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8359 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8217, some c8349, some c8214, some c8354, some c8357, some c8358, some c1954, some c1063, some c655, some c1743, some c961, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8359 : lratChecker f8359 p8359 = .success := by decide +kernel
theorem unsat8359 : Unsatisfiable (PosFin 65) f8359 := by
  apply lratCheckerSound f8359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8359
  · intro a ha; simp [p8359] at ha; subst a; trivial
  · exact checked8359
theorem derived8359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8359 := by
  apply localUnsat_implies_entails f8359 [c8124, c8217, c8349, c8214, c8354, c8357, c8358, c1954, c1063, c655, c1743, c961] c8359 unsat8359 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8217 := derived8217 a h
  have h2 : Entails.eval a c8349 := derived8349 a h
  have h3 : Entails.eval a c8214 := derived8214 a h
  have h4 : Entails.eval a c8354 := derived8354 a h
  have h5 : Entails.eval a c8357 := derived8357 a h
  have h6 : Entails.eval a c8358 := derived8358 a h
  have h7 : Entails.eval a c1954 := h 1953 (by decide)
  have h8 : Entails.eval a c1063 := h 1062 (by decide)
  have h9 : Entails.eval a c655 := h 654 (by decide)
  have h10 : Entails.eval a c1743 := h 1742 (by decide)
  have h11 : Entails.eval a c961 := h 960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8360 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2244, some c2263, some c2260, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8360 : lratChecker f8360 p8360 = .success := by decide +kernel
theorem unsat8360 : Unsatisfiable (PosFin 65) f8360 := by
  apply lratCheckerSound f8360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8360
  · intro a ha; simp [p8360] at ha; subst a; trivial
  · exact checked8360
theorem derived8360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8360 := by
  apply localUnsat_implies_entails f8360 [c2244, c2263, c2260] c8360 unsat8360 (by rfl) a
  have h0 : Entails.eval a c2244 := h 2243 (by decide)
  have h1 : Entails.eval a c2263 := h 2262 (by decide)
  have h2 : Entails.eval a c2260 := h 2259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8361 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8348, some c8317, some c8159, some c7849, some c8355, some c8359, some c8360, some c8309, some c8240, some c8352, some c8354, some c8312, some c8358, some c2369, some c2524, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8361 : lratChecker f8361 p8361 = .success := by decide +kernel
theorem unsat8361 : Unsatisfiable (PosFin 65) f8361 := by
  apply lratCheckerSound f8361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8361
  · intro a ha; simp [p8361] at ha; subst a; trivial
  · exact checked8361
theorem derived8361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8361 := by
  apply localUnsat_implies_entails f8361 [c8348, c8317, c8159, c7849, c8355, c8359, c8360, c8309, c8240, c8352, c8354, c8312, c8358, c2369, c2524] c8361 unsat8361 (by rfl) a
  have h0 : Entails.eval a c8348 := derived8348 a h
  have h1 : Entails.eval a c8317 := derived8317 a h
  have h2 : Entails.eval a c8159 := derived8159 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8355 := derived8355 a h
  have h5 : Entails.eval a c8359 := derived8359 a h
  have h6 : Entails.eval a c8360 := derived8360 a h
  have h7 : Entails.eval a c8309 := derived8309 a h
  have h8 : Entails.eval a c8240 := derived8240 a h
  have h9 : Entails.eval a c8352 := derived8352 a h
  have h10 : Entails.eval a c8354 := derived8354 a h
  have h11 : Entails.eval a c8312 := derived8312 a h
  have h12 : Entails.eval a c8358 := derived8358 a h
  have h13 : Entails.eval a c2369 := h 2368 (by decide)
  have h14 : Entails.eval a c2524 := h 2523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8362 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8219, some c8124, some c8217, some c8168, some c8186, some c8353, some c8354, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8362 : lratChecker f8362 p8362 = .success := by decide +kernel
theorem unsat8362 : Unsatisfiable (PosFin 65) f8362 := by
  apply lratCheckerSound f8362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8362
  · intro a ha; simp [p8362] at ha; subst a; trivial
  · exact checked8362
theorem derived8362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8362 := by
  apply localUnsat_implies_entails f8362 [c8219, c8124, c8217, c8168, c8186, c8353, c8354] c8362 unsat8362 (by rfl) a
  have h0 : Entails.eval a c8219 := derived8219 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8217 := derived8217 a h
  have h3 : Entails.eval a c8168 := derived8168 a h
  have h4 : Entails.eval a c8186 := derived8186 a h
  have h5 : Entails.eval a c8353 := derived8353 a h
  have h6 : Entails.eval a c8354 := derived8354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8363 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c497, some c498, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8363 : lratChecker f8363 p8363 = .success := by decide +kernel
theorem unsat8363 : Unsatisfiable (PosFin 65) f8363 := by
  apply lratCheckerSound f8363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8363
  · intro a ha; simp [p8363] at ha; subst a; trivial
  · exact checked8363
theorem derived8363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8363 := by
  apply localUnsat_implies_entails f8363 [c497, c498] c8363 unsat8363 (by rfl) a
  have h0 : Entails.eval a c497 := h 496 (by decide)
  have h1 : Entails.eval a c498 := h 497 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8364 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2479, some c8150, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8364 : lratChecker f8364 p8364 = .success := by decide +kernel
theorem unsat8364 : Unsatisfiable (PosFin 65) f8364 := by
  apply lratCheckerSound f8364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8364
  · intro a ha; simp [p8364] at ha; subst a; trivial
  · exact checked8364
theorem derived8364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8364 := by
  apply localUnsat_implies_entails f8364 [c2479, c8150] c8364 unsat8364 (by rfl) a
  have h0 : Entails.eval a c2479 := h 2478 (by decide)
  have h1 : Entails.eval a c8150 := derived8150 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8365 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8362, some c8351, some c8285, some c8286, some c8287, some c8288, some c8363, some c8364, some c1594, some c1844, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8365 : lratChecker f8365 p8365 = .success := by decide +kernel
theorem unsat8365 : Unsatisfiable (PosFin 65) f8365 := by
  apply lratCheckerSound f8365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8365
  · intro a ha; simp [p8365] at ha; subst a; trivial
  · exact checked8365
theorem derived8365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8365 := by
  apply localUnsat_implies_entails f8365 [c8362, c8351, c8285, c8286, c8287, c8288, c8363, c8364, c1594, c1844] c8365 unsat8365 (by rfl) a
  have h0 : Entails.eval a c8362 := derived8362 a h
  have h1 : Entails.eval a c8351 := derived8351 a h
  have h2 : Entails.eval a c8285 := derived8285 a h
  have h3 : Entails.eval a c8286 := derived8286 a h
  have h4 : Entails.eval a c8287 := derived8287 a h
  have h5 : Entails.eval a c8288 := derived8288 a h
  have h6 : Entails.eval a c8363 := derived8363 a h
  have h7 : Entails.eval a c8364 := derived8364 a h
  have h8 : Entails.eval a c1594 := h 1593 (by decide)
  have h9 : Entails.eval a c1844 := h 1843 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8366 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8362, some c8351, some c8285, some c8286, some c8365, some c8353, some c8292, some c1886, some c1825, some c1847, some c1849, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8366 : lratChecker f8366 p8366 = .success := by decide +kernel
theorem unsat8366 : Unsatisfiable (PosFin 65) f8366 := by
  apply lratCheckerSound f8366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8366
  · intro a ha; simp [p8366] at ha; subst a; trivial
  · exact checked8366
theorem derived8366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8366 := by
  apply localUnsat_implies_entails f8366 [c8362, c8351, c8285, c8286, c8365, c8353, c8292, c1886, c1825, c1847, c1849] c8366 unsat8366 (by rfl) a
  have h0 : Entails.eval a c8362 := derived8362 a h
  have h1 : Entails.eval a c8351 := derived8351 a h
  have h2 : Entails.eval a c8285 := derived8285 a h
  have h3 : Entails.eval a c8286 := derived8286 a h
  have h4 : Entails.eval a c8365 := derived8365 a h
  have h5 : Entails.eval a c8353 := derived8353 a h
  have h6 : Entails.eval a c8292 := derived8292 a h
  have h7 : Entails.eval a c1886 := h 1885 (by decide)
  have h8 : Entails.eval a c1825 := h 1824 (by decide)
  have h9 : Entails.eval a c1847 := h 1846 (by decide)
  have h10 : Entails.eval a c1849 := h 1848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8367 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c493, some c498, some c503, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8367 : lratChecker f8367 p8367 = .success := by decide +kernel
theorem unsat8367 : Unsatisfiable (PosFin 65) f8367 := by
  apply lratCheckerSound f8367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8367
  · intro a ha; simp [p8367] at ha; subst a; trivial
  · exact checked8367
theorem derived8367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8367 := by
  apply localUnsat_implies_entails f8367 [c493, c498, c503] c8367 unsat8367 (by rfl) a
  have h0 : Entails.eval a c493 := h 492 (by decide)
  have h1 : Entails.eval a c498 := h 497 (by decide)
  have h2 : Entails.eval a c503 := h 502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8368 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8362, some c8351, some c8367, some c497, some c8296, some c8304, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8368 : lratChecker f8368 p8368 = .success := by decide +kernel
theorem unsat8368 : Unsatisfiable (PosFin 65) f8368 := by
  apply lratCheckerSound f8368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8368
  · intro a ha; simp [p8368] at ha; subst a; trivial
  · exact checked8368
theorem derived8368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8368 := by
  apply localUnsat_implies_entails f8368 [c8366, c8362, c8351, c8367, c497, c8296, c8304] c8368 unsat8368 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8362 := derived8362 a h
  have h2 : Entails.eval a c8351 := derived8351 a h
  have h3 : Entails.eval a c8367 := derived8367 a h
  have h4 : Entails.eval a c497 := h 496 (by decide)
  have h5 : Entails.eval a c8296 := derived8296 a h
  have h6 : Entails.eval a c8304 := derived8304 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8369 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2140, some c2141, some c2167, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8369 : lratChecker f8369 p8369 = .success := by decide +kernel
theorem unsat8369 : Unsatisfiable (PosFin 65) f8369 := by
  apply lratCheckerSound f8369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8369
  · intro a ha; simp [p8369] at ha; subst a; trivial
  · exact checked8369
theorem derived8369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8369 := by
  apply localUnsat_implies_entails f8369 [c2140, c2141, c2167] c8369 unsat8369 (by rfl) a
  have h0 : Entails.eval a c2140 := h 2139 (by decide)
  have h1 : Entails.eval a c2141 := h 2140 (by decide)
  have h2 : Entails.eval a c2167 := h 2166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8370 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8366, some c8362, some c8351, some c8368, some c8369, some c2118, some c2001, some c2163, some c1690, some c2146, some c8296, some c1886, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8370 : lratChecker f8370 p8370 = .success := by decide +kernel
theorem unsat8370 : Unsatisfiable (PosFin 65) f8370 := by
  apply lratCheckerSound f8370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8370
  · intro a ha; simp [p8370] at ha; subst a; trivial
  · exact checked8370
theorem derived8370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8370 := by
  apply localUnsat_implies_entails f8370 [c8366, c8362, c8351, c8368, c8369, c2118, c2001, c2163, c1690, c2146, c8296, c1886] c8370 unsat8370 (by rfl) a
  have h0 : Entails.eval a c8366 := derived8366 a h
  have h1 : Entails.eval a c8362 := derived8362 a h
  have h2 : Entails.eval a c8351 := derived8351 a h
  have h3 : Entails.eval a c8368 := derived8368 a h
  have h4 : Entails.eval a c8369 := derived8369 a h
  have h5 : Entails.eval a c2118 := h 2117 (by decide)
  have h6 : Entails.eval a c2001 := h 2000 (by decide)
  have h7 : Entails.eval a c2163 := h 2162 (by decide)
  have h8 : Entails.eval a c1690 := h 1689 (by decide)
  have h9 : Entails.eval a c2146 := h 2145 (by decide)
  have h10 : Entails.eval a c8296 := derived8296 a h
  have h11 : Entails.eval a c1886 := h 1885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8371 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8362, some c8351, some c8366, some c8370, some c8353, some c8354, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8371 : lratChecker f8371 p8371 = .success := by decide +kernel
theorem unsat8371 : Unsatisfiable (PosFin 65) f8371 := by
  apply lratCheckerSound f8371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8371
  · intro a ha; simp [p8371] at ha; subst a; trivial
  · exact checked8371
theorem derived8371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8371 := by
  apply localUnsat_implies_entails f8371 [c8362, c8351, c8366, c8370, c8353, c8354] c8371 unsat8371 (by rfl) a
  have h0 : Entails.eval a c8362 := derived8362 a h
  have h1 : Entails.eval a c8351 := derived8351 a h
  have h2 : Entails.eval a c8366 := derived8366 a h
  have h3 : Entails.eval a c8370 := derived8370 a h
  have h4 : Entails.eval a c8353 := derived8353 a h
  have h5 : Entails.eval a c8354 := derived8354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8372 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8371, some c8219, some c8124, some c8217, some c8168, some c8186, some c8354, some c8358, some c1954, some c2530, some c1743, some c1876, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8372 : lratChecker f8372 p8372 = .success := by decide +kernel
theorem unsat8372 : Unsatisfiable (PosFin 65) f8372 := by
  apply lratCheckerSound f8372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8372
  · intro a ha; simp [p8372] at ha; subst a; trivial
  · exact checked8372
theorem derived8372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8372 := by
  apply localUnsat_implies_entails f8372 [c8371, c8219, c8124, c8217, c8168, c8186, c8354, c8358, c1954, c2530, c1743, c1876] c8372 unsat8372 (by rfl) a
  have h0 : Entails.eval a c8371 := derived8371 a h
  have h1 : Entails.eval a c8219 := derived8219 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8217 := derived8217 a h
  have h4 : Entails.eval a c8168 := derived8168 a h
  have h5 : Entails.eval a c8186 := derived8186 a h
  have h6 : Entails.eval a c8354 := derived8354 a h
  have h7 : Entails.eval a c8358 := derived8358 a h
  have h8 : Entails.eval a c1954 := h 1953 (by decide)
  have h9 : Entails.eval a c2530 := h 2529 (by decide)
  have h10 : Entails.eval a c1743 := h 1742 (by decide)
  have h11 : Entails.eval a c1876 := h 1875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8373 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2261, some c2263, some c2260, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8373 : lratChecker f8373 p8373 = .success := by decide +kernel
theorem unsat8373 : Unsatisfiable (PosFin 65) f8373 := by
  apply lratCheckerSound f8373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8373
  · intro a ha; simp [p8373] at ha; subst a; trivial
  · exact checked8373
theorem derived8373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8373 := by
  apply localUnsat_implies_entails f8373 [c2261, c2263, c2260] c8373 unsat8373 (by rfl) a
  have h0 : Entails.eval a c2261 := h 2260 (by decide)
  have h1 : Entails.eval a c2263 := h 2262 (by decide)
  have h2 : Entails.eval a c2260 := h 2259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8374 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2399, some c2404, some c2398, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8374 : lratChecker f8374 p8374 = .success := by decide +kernel
theorem unsat8374 : Unsatisfiable (PosFin 65) f8374 := by
  apply lratCheckerSound f8374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8374
  · intro a ha; simp [p8374] at ha; subst a; trivial
  · exact checked8374
theorem derived8374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8374 := by
  apply localUnsat_implies_entails f8374 [c2399, c2404, c2398] c8374 unsat8374 (by rfl) a
  have h0 : Entails.eval a c2399 := h 2398 (by decide)
  have h1 : Entails.eval a c2404 := h 2403 (by decide)
  have h2 : Entails.eval a c2398 := h 2397 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8375 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c665, some c666, some c668, some c662, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p8375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8375 : lratChecker f8375 p8375 = .success := by decide +kernel
theorem unsat8375 : Unsatisfiable (PosFin 65) f8375 := by
  apply lratCheckerSound f8375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8375
  · intro a ha; simp [p8375] at ha; subst a; trivial
  · exact checked8375
theorem derived8375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8375 := by
  apply localUnsat_implies_entails f8375 [c665, c666, c668, c662] c8375 unsat8375 (by rfl) a
  have h0 : Entails.eval a c665 := h 664 (by decide)
  have h1 : Entails.eval a c666 := h 665 (by decide)
  have h2 : Entails.eval a c668 := h 667 (by decide)
  have h3 : Entails.eval a c662 := h 661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8376 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8371, some c8372, some c8373, some c8374, some c8375, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8376 : lratChecker f8376 p8376 = .success := by decide +kernel
theorem unsat8376 : Unsatisfiable (PosFin 65) f8376 := by
  apply lratCheckerSound f8376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8376
  · intro a ha; simp [p8376] at ha; subst a; trivial
  · exact checked8376
theorem derived8376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8376 := by
  apply localUnsat_implies_entails f8376 [c8371, c8372, c8373, c8374, c8375] c8376 unsat8376 (by rfl) a
  have h0 : Entails.eval a c8371 := derived8371 a h
  have h1 : Entails.eval a c8372 := derived8372 a h
  have h2 : Entails.eval a c8373 := derived8373 a h
  have h3 : Entails.eval a c8374 := derived8374 a h
  have h4 : Entails.eval a c8375 := derived8375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8377 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8159, some c8317, some c8348, some c8361, some c8376, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8377 : lratChecker f8377 p8377 = .success := by decide +kernel
theorem unsat8377 : Unsatisfiable (PosFin 65) f8377 := by
  apply lratCheckerSound f8377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8377
  · intro a ha; simp [p8377] at ha; subst a; trivial
  · exact checked8377
theorem derived8377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8377 := by
  apply localUnsat_implies_entails f8377 [c7849, c8159, c8317, c8348, c8361, c8376] c8377 unsat8377 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c8317 := derived8317 a h
  have h3 : Entails.eval a c8348 := derived8348 a h
  have h4 : Entails.eval a c8361 := derived8361 a h
  have h5 : Entails.eval a c8376 := derived8376 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8378 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c541, some c552, some c523, some c520, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8378 : lratChecker f8378 p8378 = .success := by decide +kernel
theorem unsat8378 : Unsatisfiable (PosFin 65) f8378 := by
  apply lratCheckerSound f8378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8378
  · intro a ha; simp [p8378] at ha; subst a; trivial
  · exact checked8378
theorem derived8378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8378 := by
  apply localUnsat_implies_entails f8378 [c541, c552, c523, c520] c8378 unsat8378 (by rfl) a
  have h0 : Entails.eval a c541 := h 540 (by decide)
  have h1 : Entails.eval a c552 := h 551 (by decide)
  have h2 : Entails.eval a c523 := h 522 (by decide)
  have h3 : Entails.eval a c520 := h 519 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8379 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8377, some c8378, some c8116, some c7961, some c518, some c539, some c520, some c2268, some c2269, some c3072, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8379 : lratChecker f8379 p8379 = .success := by decide +kernel
theorem unsat8379 : Unsatisfiable (PosFin 65) f8379 := by
  apply lratCheckerSound f8379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8379
  · intro a ha; simp [p8379] at ha; subst a; trivial
  · exact checked8379
theorem derived8379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8379 := by
  apply localUnsat_implies_entails f8379 [c7849, c8377, c8378, c8116, c7961, c518, c539, c520, c2268, c2269, c3072] c8379 unsat8379 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8377 := derived8377 a h
  have h2 : Entails.eval a c8378 := derived8378 a h
  have h3 : Entails.eval a c8116 := derived8116 a h
  have h4 : Entails.eval a c7961 := derived7961 a h
  have h5 : Entails.eval a c518 := h 517 (by decide)
  have h6 : Entails.eval a c539 := h 538 (by decide)
  have h7 : Entails.eval a c520 := h 519 (by decide)
  have h8 : Entails.eval a c2268 := h 2267 (by decide)
  have h9 : Entails.eval a c2269 := h 2268 (by decide)
  have h10 : Entails.eval a c3072 := h 3071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8380 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true), (⟨27, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8377, some c7849, some c8378, some c7961, some c8116, some c518, some c539, some c864, some c7982, some c547, some c451, some c855, some c8379, some c2079, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8380 : lratChecker f8380 p8380 = .success := by decide +kernel
theorem unsat8380 : Unsatisfiable (PosFin 65) f8380 := by
  apply lratCheckerSound f8380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8380
  · intro a ha; simp [p8380] at ha; subst a; trivial
  · exact checked8380
theorem derived8380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8380 := by
  apply localUnsat_implies_entails f8380 [c8377, c7849, c8378, c7961, c8116, c518, c539, c864, c7982, c547, c451, c855, c8379, c2079] c8380 unsat8380 (by rfl) a
  have h0 : Entails.eval a c8377 := derived8377 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8378 := derived8378 a h
  have h3 : Entails.eval a c7961 := derived7961 a h
  have h4 : Entails.eval a c8116 := derived8116 a h
  have h5 : Entails.eval a c518 := h 517 (by decide)
  have h6 : Entails.eval a c539 := h 538 (by decide)
  have h7 : Entails.eval a c864 := h 863 (by decide)
  have h8 : Entails.eval a c7982 := derived7982 a h
  have h9 : Entails.eval a c547 := h 546 (by decide)
  have h10 : Entails.eval a c451 := h 450 (by decide)
  have h11 : Entails.eval a c855 := h 854 (by decide)
  have h12 : Entails.eval a c8379 := derived8379 a h
  have h13 : Entails.eval a c2079 := h 2078 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8380

end CochromaticTwenty.Certificates.FixedCore1
