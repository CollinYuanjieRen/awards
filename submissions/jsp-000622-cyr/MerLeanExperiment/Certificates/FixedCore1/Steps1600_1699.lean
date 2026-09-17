import MerLeanExperiment.Certificates.FixedCore1.Steps1500_1599

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7481 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7481 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7224, some c2407, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7481 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7481 : lratChecker f7481 p7481 = .success := by decide +kernel
theorem unsat7481 : Unsatisfiable (PosFin 65) f7481 := by
  apply lratCheckerSound f7481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7481
  · intro a ha; simp [p7481] at ha; subst a; trivial
  · exact checked7481
theorem derived7481 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7481 := by
  apply localUnsat_implies_entails f7481 [c7224, c2407] c7481 unsat7481 (by rfl) a
  have h0 : Entails.eval a c7224 := derived7224 a h
  have h1 : Entails.eval a c2407 := h 2406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7482 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7482 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1466, some c1502, some c1215, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7482 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7482 : lratChecker f7482 p7482 = .success := by decide +kernel
theorem unsat7482 : Unsatisfiable (PosFin 65) f7482 := by
  apply lratCheckerSound f7482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7482
  · intro a ha; simp [p7482] at ha; subst a; trivial
  · exact checked7482
theorem derived7482 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7482 := by
  apply localUnsat_implies_entails f7482 [c1466, c1502, c1215] c7482 unsat7482 (by rfl) a
  have h0 : Entails.eval a c1466 := h 1465 (by decide)
  have h1 : Entails.eval a c1502 := h 1501 (by decide)
  have h2 : Entails.eval a c1215 := h 1214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7483 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7483 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2280, some c7482, some c903, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7483 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7483 : lratChecker f7483 p7483 = .success := by decide +kernel
theorem unsat7483 : Unsatisfiable (PosFin 65) f7483 := by
  apply lratCheckerSound f7483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7483
  · intro a ha; simp [p7483] at ha; subst a; trivial
  · exact checked7483
theorem derived7483 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7483 := by
  apply localUnsat_implies_entails f7483 [c2280, c7482, c903] c7483 unsat7483 (by rfl) a
  have h0 : Entails.eval a c2280 := h 2279 (by decide)
  have h1 : Entails.eval a c7482 := derived7482 a h
  have h2 : Entails.eval a c903 := h 902 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7484 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7484 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c752, some c776, some c761, some c777, some c753, some c772, some c763, some c767, some c758, some c7480, some c7483, some c7431, some c7481, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7484 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7484 : lratChecker f7484 p7484 = .success := by decide +kernel
theorem unsat7484 : Unsatisfiable (PosFin 65) f7484 := by
  apply lratCheckerSound f7484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7484
  · intro a ha; simp [p7484] at ha; subst a; trivial
  · exact checked7484
theorem derived7484 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7484 := by
  apply localUnsat_implies_entails f7484 [c752, c776, c761, c777, c753, c772, c763, c767, c758, c7480, c7483, c7431, c7481] c7484 unsat7484 (by rfl) a
  have h0 : Entails.eval a c752 := h 751 (by decide)
  have h1 : Entails.eval a c776 := h 775 (by decide)
  have h2 : Entails.eval a c761 := h 760 (by decide)
  have h3 : Entails.eval a c777 := h 776 (by decide)
  have h4 : Entails.eval a c753 := h 752 (by decide)
  have h5 : Entails.eval a c772 := h 771 (by decide)
  have h6 : Entails.eval a c763 := h 762 (by decide)
  have h7 : Entails.eval a c767 := h 766 (by decide)
  have h8 : Entails.eval a c758 := h 757 (by decide)
  have h9 : Entails.eval a c7480 := derived7480 a h
  have h10 : Entails.eval a c7483 := derived7483 a h
  have h11 : Entails.eval a c7431 := derived7431 a h
  have h12 : Entails.eval a c7481 := derived7481 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7485 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7485 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1058, some c903, some c2228, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7485 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7485 : lratChecker f7485 p7485 = .success := by decide +kernel
theorem unsat7485 : Unsatisfiable (PosFin 65) f7485 := by
  apply lratCheckerSound f7485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7485
  · intro a ha; simp [p7485] at ha; subst a; trivial
  · exact checked7485
theorem derived7485 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7485 := by
  apply localUnsat_implies_entails f7485 [c1058, c903, c2228] c7485 unsat7485 (by rfl) a
  have h0 : Entails.eval a c1058 := h 1057 (by decide)
  have h1 : Entails.eval a c903 := h 902 (by decide)
  have h2 : Entails.eval a c2228 := h 2227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7486 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7486 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c812, some c1136, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7486 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7486 : lratChecker f7486 p7486 = .success := by decide +kernel
theorem unsat7486 : Unsatisfiable (PosFin 65) f7486 := by
  apply lratCheckerSound f7486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7486
  · intro a ha; simp [p7486] at ha; subst a; trivial
  · exact checked7486
theorem derived7486 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7486 := by
  apply localUnsat_implies_entails f7486 [c812, c1136] c7486 unsat7486 (by rfl) a
  have h0 : Entails.eval a c812 := h 811 (by decide)
  have h1 : Entails.eval a c1136 := h 1135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7487 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7487 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1243, some c1256, some c1218, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7487 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7487 : lratChecker f7487 p7487 = .success := by decide +kernel
theorem unsat7487 : Unsatisfiable (PosFin 65) f7487 := by
  apply lratCheckerSound f7487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7487
  · intro a ha; simp [p7487] at ha; subst a; trivial
  · exact checked7487
theorem derived7487 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7487 := by
  apply localUnsat_implies_entails f7487 [c1243, c1256, c1218] c7487 unsat7487 (by rfl) a
  have h0 : Entails.eval a c1243 := h 1242 (by decide)
  have h1 : Entails.eval a c1256 := h 1255 (by decide)
  have h2 : Entails.eval a c1218 := h 1217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7488 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7488 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c293, some c311, some c294, some c7487, some c1247, some c1259, some c1221, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7488 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7488 : lratChecker f7488 p7488 = .success := by decide +kernel
theorem unsat7488 : Unsatisfiable (PosFin 65) f7488 := by
  apply lratCheckerSound f7488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7488
  · intro a ha; simp [p7488] at ha; subst a; trivial
  · exact checked7488
theorem derived7488 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7488 := by
  apply localUnsat_implies_entails f7488 [c293, c311, c294, c7487, c1247, c1259, c1221] c7488 unsat7488 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c7487 := derived7487 a h
  have h4 : Entails.eval a c1247 := h 1246 (by decide)
  have h5 : Entails.eval a c1259 := h 1258 (by decide)
  have h6 : Entails.eval a c1221 := h 1220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7489 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7489 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1055, some c1110, some c2538, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7489 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7489 : lratChecker f7489 p7489 = .success := by decide +kernel
theorem unsat7489 : Unsatisfiable (PosFin 65) f7489 := by
  apply lratCheckerSound f7489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7489
  · intro a ha; simp [p7489] at ha; subst a; trivial
  · exact checked7489
theorem derived7489 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7489 := by
  apply localUnsat_implies_entails f7489 [c1055, c1110, c2538] c7489 unsat7489 (by rfl) a
  have h0 : Entails.eval a c1055 := h 1054 (by decide)
  have h1 : Entails.eval a c1110 := h 1109 (by decide)
  have h2 : Entails.eval a c2538 := h 2537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7490 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7490 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7485, some c981, some c1073, some c2018, some c2041, some c2616, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7490 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7490 : lratChecker f7490 p7490 = .success := by decide +kernel
theorem unsat7490 : Unsatisfiable (PosFin 65) f7490 := by
  apply lratCheckerSound f7490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7490
  · intro a ha; simp [p7490] at ha; subst a; trivial
  · exact checked7490
theorem derived7490 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7490 := by
  apply localUnsat_implies_entails f7490 [c7485, c981, c1073, c2018, c2041, c2616] c7490 unsat7490 (by rfl) a
  have h0 : Entails.eval a c7485 := derived7485 a h
  have h1 : Entails.eval a c981 := h 980 (by decide)
  have h2 : Entails.eval a c1073 := h 1072 (by decide)
  have h3 : Entails.eval a c2018 := h 2017 (by decide)
  have h4 : Entails.eval a c2041 := h 2040 (by decide)
  have h5 : Entails.eval a c2616 := h 2615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7491 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7491 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7484, some c7489, some c789, some c1118, some c2623, some c2547, some c1073, some c1053, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7491 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7491 : lratChecker f7491 p7491 = .success := by decide +kernel
theorem unsat7491 : Unsatisfiable (PosFin 65) f7491 := by
  apply lratCheckerSound f7491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7491
  · intro a ha; simp [p7491] at ha; subst a; trivial
  · exact checked7491
theorem derived7491 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7491 := by
  apply localUnsat_implies_entails f7491 [c7484, c7489, c789, c1118, c2623, c2547, c1073, c1053] c7491 unsat7491 (by rfl) a
  have h0 : Entails.eval a c7484 := derived7484 a h
  have h1 : Entails.eval a c7489 := derived7489 a h
  have h2 : Entails.eval a c789 := h 788 (by decide)
  have h3 : Entails.eval a c1118 := h 1117 (by decide)
  have h4 : Entails.eval a c2623 := h 2622 (by decide)
  have h5 : Entails.eval a c2547 := h 2546 (by decide)
  have h6 : Entails.eval a c1073 := h 1072 (by decide)
  have h7 : Entails.eval a c1053 := h 1052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7492 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7492 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7484, some c7486, some c7489, some c7491, some c7490, some c7488, some c1782, some c1732, some c1381, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7492 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7492 : lratChecker f7492 p7492 = .success := by decide +kernel
theorem unsat7492 : Unsatisfiable (PosFin 65) f7492 := by
  apply lratCheckerSound f7492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7492
  · intro a ha; simp [p7492] at ha; subst a; trivial
  · exact checked7492
theorem derived7492 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7492 := by
  apply localUnsat_implies_entails f7492 [c7484, c7486, c7489, c7491, c7490, c7488, c1782, c1732, c1381] c7492 unsat7492 (by rfl) a
  have h0 : Entails.eval a c7484 := derived7484 a h
  have h1 : Entails.eval a c7486 := derived7486 a h
  have h2 : Entails.eval a c7489 := derived7489 a h
  have h3 : Entails.eval a c7491 := derived7491 a h
  have h4 : Entails.eval a c7490 := derived7490 a h
  have h5 : Entails.eval a c7488 := derived7488 a h
  have h6 : Entails.eval a c1782 := h 1781 (by decide)
  have h7 : Entails.eval a c1732 := h 1731 (by decide)
  have h8 : Entails.eval a c1381 := h 1380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7493 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7493 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c752, some c776, some c755, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7493 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7493 : lratChecker f7493 p7493 = .success := by decide +kernel
theorem unsat7493 : Unsatisfiable (PosFin 65) f7493 := by
  apply lratCheckerSound f7493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7493
  · intro a ha; simp [p7493] at ha; subst a; trivial
  · exact checked7493
theorem derived7493 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7493 := by
  apply localUnsat_implies_entails f7493 [c752, c776, c755] c7493 unsat7493 (by rfl) a
  have h0 : Entails.eval a c752 := h 751 (by decide)
  have h1 : Entails.eval a c776 := h 775 (by decide)
  have h2 : Entails.eval a c755 := h 754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7494 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7494 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c12, some c43, some c2898, some c24, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7494 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7494 : lratChecker f7494 p7494 = .success := by decide +kernel
theorem unsat7494 : Unsatisfiable (PosFin 65) f7494 := by
  apply lratCheckerSound f7494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7494
  · intro a ha; simp [p7494] at ha; subst a; trivial
  · exact checked7494
theorem derived7494 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7494 := by
  apply localUnsat_implies_entails f7494 [c12, c43, c2898, c24] c7494 unsat7494 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c2898 := h 2897 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7495 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7495 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7492, some c7493, some c7486, some c7439, some c793, some c1142, some c1111, some c2616, some c1131, some c1143, some c1830, some c1816, some c1222, some c1228, some c7494, some c14, some c15, some c18, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7495 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7495 : lratChecker f7495 p7495 = .success := by decide +kernel
theorem unsat7495 : Unsatisfiable (PosFin 65) f7495 := by
  apply lratCheckerSound f7495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7495
  · intro a ha; simp [p7495] at ha; subst a; trivial
  · exact checked7495
theorem derived7495 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7495 := by
  apply localUnsat_implies_entails f7495 [c7470, c7492, c7493, c7486, c7439, c793, c1142, c1111, c2616, c1131, c1143, c1830, c1816, c1222, c1228, c7494, c14, c15, c18] c7495 unsat7495 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  have h2 : Entails.eval a c7493 := derived7493 a h
  have h3 : Entails.eval a c7486 := derived7486 a h
  have h4 : Entails.eval a c7439 := derived7439 a h
  have h5 : Entails.eval a c793 := h 792 (by decide)
  have h6 : Entails.eval a c1142 := h 1141 (by decide)
  have h7 : Entails.eval a c1111 := h 1110 (by decide)
  have h8 : Entails.eval a c2616 := h 2615 (by decide)
  have h9 : Entails.eval a c1131 := h 1130 (by decide)
  have h10 : Entails.eval a c1143 := h 1142 (by decide)
  have h11 : Entails.eval a c1830 := h 1829 (by decide)
  have h12 : Entails.eval a c1816 := h 1815 (by decide)
  have h13 : Entails.eval a c1222 := h 1221 (by decide)
  have h14 : Entails.eval a c1228 := h 1227 (by decide)
  have h15 : Entails.eval a c7494 := derived7494 a h
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7496 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7496 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6743, some c6742, some c105, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7496 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7496 : lratChecker f7496 p7496 = .success := by decide +kernel
theorem unsat7496 : Unsatisfiable (PosFin 65) f7496 := by
  apply lratCheckerSound f7496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7496
  · intro a ha; simp [p7496] at ha; subst a; trivial
  · exact checked7496
theorem derived7496 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7496 := by
  apply localUnsat_implies_entails f7496 [c6743, c6742, c105] c7496 unsat7496 (by rfl) a
  have h0 : Entails.eval a c6743 := derived6743 a h
  have h1 : Entails.eval a c6742 := derived6742 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7497 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7497 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7492, some c7493, some c7486, some c7495, some c7375, some c789, some c1142, some c2623, some c1111, some c1131, some c1143, some c2547, some c1820, some c1838, some c1059, some c1067, some c1144, some c2518, some c7496, some c14, some c15, some c18, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7497 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked7497 : lratChecker f7497 p7497 = .success := by decide +kernel
theorem unsat7497 : Unsatisfiable (PosFin 65) f7497 := by
  apply lratCheckerSound f7497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7497
  · intro a ha; simp [p7497] at ha; subst a; trivial
  · exact checked7497
theorem derived7497 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7497 := by
  apply localUnsat_implies_entails f7497 [c7470, c7492, c7493, c7486, c7495, c7375, c789, c1142, c2623, c1111, c1131, c1143, c2547, c1820, c1838, c1059, c1067, c1144, c2518, c7496, c14, c15, c18] c7497 unsat7497 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7492 := derived7492 a h
  have h2 : Entails.eval a c7493 := derived7493 a h
  have h3 : Entails.eval a c7486 := derived7486 a h
  have h4 : Entails.eval a c7495 := derived7495 a h
  have h5 : Entails.eval a c7375 := derived7375 a h
  have h6 : Entails.eval a c789 := h 788 (by decide)
  have h7 : Entails.eval a c1142 := h 1141 (by decide)
  have h8 : Entails.eval a c2623 := h 2622 (by decide)
  have h9 : Entails.eval a c1111 := h 1110 (by decide)
  have h10 : Entails.eval a c1131 := h 1130 (by decide)
  have h11 : Entails.eval a c1143 := h 1142 (by decide)
  have h12 : Entails.eval a c2547 := h 2546 (by decide)
  have h13 : Entails.eval a c1820 := h 1819 (by decide)
  have h14 : Entails.eval a c1838 := h 1837 (by decide)
  have h15 : Entails.eval a c1059 := h 1058 (by decide)
  have h16 : Entails.eval a c1067 := h 1066 (by decide)
  have h17 : Entails.eval a c1144 := h 1143 (by decide)
  have h18 : Entails.eval a c2518 := h 2517 (by decide)
  have h19 : Entails.eval a c7496 := derived7496 a h
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7498 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7498 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c762, some c778, some c2285, some c763, some c1019, some c899, some c1255, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7498 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7498 : lratChecker f7498 p7498 = .success := by decide +kernel
theorem unsat7498 : Unsatisfiable (PosFin 65) f7498 := by
  apply lratCheckerSound f7498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7498
  · intro a ha; simp [p7498] at ha; subst a; trivial
  · exact checked7498
theorem derived7498 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7498 := by
  apply localUnsat_implies_entails f7498 [c762, c778, c2285, c763, c1019, c899, c1255] c7498 unsat7498 (by rfl) a
  have h0 : Entails.eval a c762 := h 761 (by decide)
  have h1 : Entails.eval a c778 := h 777 (by decide)
  have h2 : Entails.eval a c2285 := h 2284 (by decide)
  have h3 : Entails.eval a c763 := h 762 (by decide)
  have h4 : Entails.eval a c1019 := h 1018 (by decide)
  have h5 : Entails.eval a c899 := h 898 (by decide)
  have h6 : Entails.eval a c1255 := h 1254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7499 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7499 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7498, some c770, some c774, some c753, some c2284, some c7262, some c906, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7499 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7499 : lratChecker f7499 p7499 = .success := by decide +kernel
theorem unsat7499 : Unsatisfiable (PosFin 65) f7499 := by
  apply lratCheckerSound f7499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7499
  · intro a ha; simp [p7499] at ha; subst a; trivial
  · exact checked7499
theorem derived7499 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7499 := by
  apply localUnsat_implies_entails f7499 [c7498, c770, c774, c753, c2284, c7262, c906] c7499 unsat7499 (by rfl) a
  have h0 : Entails.eval a c7498 := derived7498 a h
  have h1 : Entails.eval a c770 := h 769 (by decide)
  have h2 : Entails.eval a c774 := h 773 (by decide)
  have h3 : Entails.eval a c753 := h 752 (by decide)
  have h4 : Entails.eval a c2284 := h 2283 (by decide)
  have h5 : Entails.eval a c7262 := derived7262 a h
  have h6 : Entails.eval a c906 := h 905 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7500 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7500 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c753, some c2280, some c762, some c778, some c1017, some c903, some c1254, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7500 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7500 : lratChecker f7500 p7500 = .success := by decide +kernel
theorem unsat7500 : Unsatisfiable (PosFin 65) f7500 := by
  apply lratCheckerSound f7500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7500
  · intro a ha; simp [p7500] at ha; subst a; trivial
  · exact checked7500
theorem derived7500 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7500 := by
  apply localUnsat_implies_entails f7500 [c753, c2280, c762, c778, c1017, c903, c1254] c7500 unsat7500 (by rfl) a
  have h0 : Entails.eval a c753 := h 752 (by decide)
  have h1 : Entails.eval a c2280 := h 2279 (by decide)
  have h2 : Entails.eval a c762 := h 761 (by decide)
  have h3 : Entails.eval a c778 := h 777 (by decide)
  have h4 : Entails.eval a c1017 := h 1016 (by decide)
  have h5 : Entails.eval a c903 := h 902 (by decide)
  have h6 : Entails.eval a c1254 := h 1253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7501 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7501 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c762, some c765, some c774, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7501 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7501 : lratChecker f7501 p7501 = .success := by decide +kernel
theorem unsat7501 : Unsatisfiable (PosFin 65) f7501 := by
  apply lratCheckerSound f7501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7501
  · intro a ha; simp [p7501] at ha; subst a; trivial
  · exact checked7501
theorem derived7501 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7501 := by
  apply localUnsat_implies_entails f7501 [c762, c765, c774] c7501 unsat7501 (by rfl) a
  have h0 : Entails.eval a c762 := h 761 (by decide)
  have h1 : Entails.eval a c765 := h 764 (by decide)
  have h2 : Entails.eval a c774 := h 773 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7502 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7502 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c724, some c716, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7502 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7502 : lratChecker f7502 p7502 = .success := by decide +kernel
theorem unsat7502 : Unsatisfiable (PosFin 65) f7502 := by
  apply lratCheckerSound f7502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7502
  · intro a ha; simp [p7502] at ha; subst a; trivial
  · exact checked7502
theorem derived7502 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7502 := by
  apply localUnsat_implies_entails f7502 [c724, c716] c7502 unsat7502 (by rfl) a
  have h0 : Entails.eval a c724 := h 723 (by decide)
  have h1 : Entails.eval a c716 := h 715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7503 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7503 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c809, some c818, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7503 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7503 : lratChecker f7503 p7503 = .success := by decide +kernel
theorem unsat7503 : Unsatisfiable (PosFin 65) f7503 := by
  apply lratCheckerSound f7503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7503
  · intro a ha; simp [p7503] at ha; subst a; trivial
  · exact checked7503
theorem derived7503 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7503 := by
  apply localUnsat_implies_entails f7503 [c809, c818] c7503 unsat7503 (by rfl) a
  have h0 : Entails.eval a c809 := h 808 (by decide)
  have h1 : Entails.eval a c818 := h 817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7504 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7504 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1303, some c2279, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7504 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7504 : lratChecker f7504 p7504 = .success := by decide +kernel
theorem unsat7504 : Unsatisfiable (PosFin 65) f7504 := by
  apply lratCheckerSound f7504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7504
  · intro a ha; simp [p7504] at ha; subst a; trivial
  · exact checked7504
theorem derived7504 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7504 := by
  apply localUnsat_implies_entails f7504 [c1303, c2279] c7504 unsat7504 (by rfl) a
  have h0 : Entails.eval a c1303 := h 1302 (by decide)
  have h1 : Entails.eval a c2279 := h 2278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7505 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7505 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c929, some c912, some c2275, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7505 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7505 : lratChecker f7505 p7505 = .success := by decide +kernel
theorem unsat7505 : Unsatisfiable (PosFin 65) f7505 := by
  apply lratCheckerSound f7505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7505
  · intro a ha; simp [p7505] at ha; subst a; trivial
  · exact checked7505
theorem derived7505 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7505 := by
  apply localUnsat_implies_entails f7505 [c929, c912, c2275] c7505 unsat7505 (by rfl) a
  have h0 : Entails.eval a c929 := h 928 (by decide)
  have h1 : Entails.eval a c912 := h 911 (by decide)
  have h2 : Entails.eval a c2275 := h 2274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7506 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7506 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1237, some c2314, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7506 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7506 : lratChecker f7506 p7506 = .success := by decide +kernel
theorem unsat7506 : Unsatisfiable (PosFin 65) f7506 := by
  apply lratCheckerSound f7506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7506
  · intro a ha; simp [p7506] at ha; subst a; trivial
  · exact checked7506
theorem derived7506 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7506 := by
  apply localUnsat_implies_entails f7506 [c1237, c2314] c7506 unsat7506 (by rfl) a
  have h0 : Entails.eval a c1237 := h 1236 (by decide)
  have h1 : Entails.eval a c2314 := h 2313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7507 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7507 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7505, some c7506, some c2344, some c1152, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7507 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7507 : lratChecker f7507 p7507 = .success := by decide +kernel
theorem unsat7507 : Unsatisfiable (PosFin 65) f7507 := by
  apply lratCheckerSound f7507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7507
  · intro a ha; simp [p7507] at ha; subst a; trivial
  · exact checked7507
theorem derived7507 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7507 := by
  apply localUnsat_implies_entails f7507 [c7505, c7506, c2344, c1152] c7507 unsat7507 (by rfl) a
  have h0 : Entails.eval a c7505 := derived7505 a h
  have h1 : Entails.eval a c7506 := derived7506 a h
  have h2 : Entails.eval a c2344 := h 2343 (by decide)
  have h3 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7508 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7508 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c929, some c1304, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7508 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7508 : lratChecker f7508 p7508 = .success := by decide +kernel
theorem unsat7508 : Unsatisfiable (PosFin 65) f7508 := by
  apply lratCheckerSound f7508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7508
  · intro a ha; simp [p7508] at ha; subst a; trivial
  · exact checked7508
theorem derived7508 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7508 := by
  apply localUnsat_implies_entails f7508 [c929, c1304] c7508 unsat7508 (by rfl) a
  have h0 : Entails.eval a c929 := h 928 (by decide)
  have h1 : Entails.eval a c1304 := h 1303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7509 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7509 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1460, some c1865, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7509 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7509 : lratChecker f7509 p7509 = .success := by decide +kernel
theorem unsat7509 : Unsatisfiable (PosFin 65) f7509 := by
  apply lratCheckerSound f7509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7509
  · intro a ha; simp [p7509] at ha; subst a; trivial
  · exact checked7509
theorem derived7509 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7509 := by
  apply localUnsat_implies_entails f7509 [c1460, c1865] c7509 unsat7509 (by rfl) a
  have h0 : Entails.eval a c1460 := h 1459 (by decide)
  have h1 : Entails.eval a c1865 := h 1864 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7510 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7510 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7501, some c7499, some c7500, some c7262, some c781, some c775, some c771, some c763, some c778, some c774, some c7502, some c7503, some c7504, some c7507, some c7508, some c7509, some c2344, some c1152, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7510 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7510 : lratChecker f7510 p7510 = .success := by decide +kernel
theorem unsat7510 : Unsatisfiable (PosFin 65) f7510 := by
  apply lratCheckerSound f7510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7510
  · intro a ha; simp [p7510] at ha; subst a; trivial
  · exact checked7510
theorem derived7510 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7510 := by
  apply localUnsat_implies_entails f7510 [c7501, c7499, c7500, c7262, c781, c775, c771, c763, c778, c774, c7502, c7503, c7504, c7507, c7508, c7509, c2344, c1152] c7510 unsat7510 (by rfl) a
  have h0 : Entails.eval a c7501 := derived7501 a h
  have h1 : Entails.eval a c7499 := derived7499 a h
  have h2 : Entails.eval a c7500 := derived7500 a h
  have h3 : Entails.eval a c7262 := derived7262 a h
  have h4 : Entails.eval a c781 := h 780 (by decide)
  have h5 : Entails.eval a c775 := h 774 (by decide)
  have h6 : Entails.eval a c771 := h 770 (by decide)
  have h7 : Entails.eval a c763 := h 762 (by decide)
  have h8 : Entails.eval a c778 := h 777 (by decide)
  have h9 : Entails.eval a c774 := h 773 (by decide)
  have h10 : Entails.eval a c7502 := derived7502 a h
  have h11 : Entails.eval a c7503 := derived7503 a h
  have h12 : Entails.eval a c7504 := derived7504 a h
  have h13 : Entails.eval a c7507 := derived7507 a h
  have h14 : Entails.eval a c7508 := derived7508 a h
  have h15 : Entails.eval a c7509 := derived7509 a h
  have h16 : Entails.eval a c2344 := h 2343 (by decide)
  have h17 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7511 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7511 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c753, some c778, some c763, some c767, some c758, some c749, some c7483, some c2289, some c900, some c1020, some c1507, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7511 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7511 : lratChecker f7511 p7511 = .success := by decide +kernel
theorem unsat7511 : Unsatisfiable (PosFin 65) f7511 := by
  apply lratCheckerSound f7511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7511
  · intro a ha; simp [p7511] at ha; subst a; trivial
  · exact checked7511
theorem derived7511 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7511 := by
  apply localUnsat_implies_entails f7511 [c753, c778, c763, c767, c758, c749, c7483, c2289, c900, c1020, c1507] c7511 unsat7511 (by rfl) a
  have h0 : Entails.eval a c753 := h 752 (by decide)
  have h1 : Entails.eval a c778 := h 777 (by decide)
  have h2 : Entails.eval a c763 := h 762 (by decide)
  have h3 : Entails.eval a c767 := h 766 (by decide)
  have h4 : Entails.eval a c758 := h 757 (by decide)
  have h5 : Entails.eval a c749 := h 748 (by decide)
  have h6 : Entails.eval a c7483 := derived7483 a h
  have h7 : Entails.eval a c2289 := h 2288 (by decide)
  have h8 : Entails.eval a c900 := h 899 (by decide)
  have h9 : Entails.eval a c1020 := h 1019 (by decide)
  have h10 : Entails.eval a c1507 := h 1506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7512 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7512 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1159, some c2314, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7512 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7512 : lratChecker f7512 p7512 = .success := by decide +kernel
theorem unsat7512 : Unsatisfiable (PosFin 65) f7512 := by
  apply lratCheckerSound f7512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7512
  · intro a ha; simp [p7512] at ha; subst a; trivial
  · exact checked7512
theorem derived7512 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7512 := by
  apply localUnsat_implies_entails f7512 [c1159, c2314] c7512 unsat7512 (by rfl) a
  have h0 : Entails.eval a c1159 := h 1158 (by decide)
  have h1 : Entails.eval a c2314 := h 2313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7513 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7513 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7501, some c7510, some c7511, some c7262, some c781, some c775, some c771, some c763, some c7502, some c778, some c7431, some c7504, some c7508, some c774, some c7503, some c7512, some c1698, some c1459, some c2220, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7513 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7513 : lratChecker f7513 p7513 = .success := by decide +kernel
theorem unsat7513 : Unsatisfiable (PosFin 65) f7513 := by
  apply lratCheckerSound f7513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7513
  · intro a ha; simp [p7513] at ha; subst a; trivial
  · exact checked7513
theorem derived7513 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7513 := by
  apply localUnsat_implies_entails f7513 [c7501, c7510, c7511, c7262, c781, c775, c771, c763, c7502, c778, c7431, c7504, c7508, c774, c7503, c7512, c1698, c1459, c2220] c7513 unsat7513 (by rfl) a
  have h0 : Entails.eval a c7501 := derived7501 a h
  have h1 : Entails.eval a c7510 := derived7510 a h
  have h2 : Entails.eval a c7511 := derived7511 a h
  have h3 : Entails.eval a c7262 := derived7262 a h
  have h4 : Entails.eval a c781 := h 780 (by decide)
  have h5 : Entails.eval a c775 := h 774 (by decide)
  have h6 : Entails.eval a c771 := h 770 (by decide)
  have h7 : Entails.eval a c763 := h 762 (by decide)
  have h8 : Entails.eval a c7502 := derived7502 a h
  have h9 : Entails.eval a c778 := h 777 (by decide)
  have h10 : Entails.eval a c7431 := derived7431 a h
  have h11 : Entails.eval a c7504 := derived7504 a h
  have h12 : Entails.eval a c7508 := derived7508 a h
  have h13 : Entails.eval a c774 := h 773 (by decide)
  have h14 : Entails.eval a c7503 := derived7503 a h
  have h15 : Entails.eval a c7512 := derived7512 a h
  have h16 : Entails.eval a c1698 := h 1697 (by decide)
  have h17 : Entails.eval a c1459 := h 1458 (by decide)
  have h18 : Entails.eval a c2220 := h 2219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7514 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7514 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c757, some c754, some c775, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7514 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7514 : lratChecker f7514 p7514 = .success := by decide +kernel
theorem unsat7514 : Unsatisfiable (PosFin 65) f7514 := by
  apply lratCheckerSound f7514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7514
  · intro a ha; simp [p7514] at ha; subst a; trivial
  · exact checked7514
theorem derived7514 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7514 := by
  apply localUnsat_implies_entails f7514 [c757, c754, c775] c7514 unsat7514 (by rfl) a
  have h0 : Entails.eval a c757 := h 756 (by decide)
  have h1 : Entails.eval a c754 := h 753 (by decide)
  have h2 : Entails.eval a c775 := h 774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7515 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7515 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c898, some c2289, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7515 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7515 : lratChecker f7515 p7515 = .success := by decide +kernel
theorem unsat7515 : Unsatisfiable (PosFin 65) f7515 := by
  apply lratCheckerSound f7515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7515
  · intro a ha; simp [p7515] at ha; subst a; trivial
  · exact checked7515
theorem derived7515 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7515 := by
  apply localUnsat_implies_entails f7515 [c898, c2289] c7515 unsat7515 (by rfl) a
  have h0 : Entails.eval a c898 := h 897 (by decide)
  have h1 : Entails.eval a c2289 := h 2288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7516 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7516 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2343, some c1460, some c1239, some c1883, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7516 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7516 : lratChecker f7516 p7516 = .success := by decide +kernel
theorem unsat7516 : Unsatisfiable (PosFin 65) f7516 := by
  apply lratCheckerSound f7516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7516
  · intro a ha; simp [p7516] at ha; subst a; trivial
  · exact checked7516
theorem derived7516 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7516 := by
  apply localUnsat_implies_entails f7516 [c2343, c1460, c1239, c1883] c7516 unsat7516 (by rfl) a
  have h0 : Entails.eval a c2343 := h 2342 (by decide)
  have h1 : Entails.eval a c1460 := h 1459 (by decide)
  have h2 : Entails.eval a c1239 := h 1238 (by decide)
  have h3 : Entails.eval a c1883 := h 1882 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7517 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7517 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c771, some c775, some c763, some c760, some c774, some c7516, some c1459, some c888, some c1949, some c1086, some c1875, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7517 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7517 : lratChecker f7517 p7517 = .success := by decide +kernel
theorem unsat7517 : Unsatisfiable (PosFin 65) f7517 := by
  apply lratCheckerSound f7517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7517
  · intro a ha; simp [p7517] at ha; subst a; trivial
  · exact checked7517
theorem derived7517 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7517 := by
  apply localUnsat_implies_entails f7517 [c771, c775, c763, c760, c774, c7516, c1459, c888, c1949, c1086, c1875] c7517 unsat7517 (by rfl) a
  have h0 : Entails.eval a c771 := h 770 (by decide)
  have h1 : Entails.eval a c775 := h 774 (by decide)
  have h2 : Entails.eval a c763 := h 762 (by decide)
  have h3 : Entails.eval a c760 := h 759 (by decide)
  have h4 : Entails.eval a c774 := h 773 (by decide)
  have h5 : Entails.eval a c7516 := derived7516 a h
  have h6 : Entails.eval a c1459 := h 1458 (by decide)
  have h7 : Entails.eval a c888 := h 887 (by decide)
  have h8 : Entails.eval a c1949 := h 1948 (by decide)
  have h9 : Entails.eval a c1086 := h 1085 (by decide)
  have h10 : Entails.eval a c1875 := h 1874 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7518 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7518 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1460, some c7506, some c1874, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7518 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7518 : lratChecker f7518 p7518 = .success := by decide +kernel
theorem unsat7518 : Unsatisfiable (PosFin 65) f7518 := by
  apply lratCheckerSound f7518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7518
  · intro a ha; simp [p7518] at ha; subst a; trivial
  · exact checked7518
theorem derived7518 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7518 := by
  apply localUnsat_implies_entails f7518 [c1460, c7506, c1874] c7518 unsat7518 (by rfl) a
  have h0 : Entails.eval a c1460 := h 1459 (by decide)
  have h1 : Entails.eval a c7506 := derived7506 a h
  have h2 : Entails.eval a c1874 := h 1873 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7519 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7519 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c771, some c775, some c748, some c755, some c7517, some c779, some c774, some c2299, some c7518, some c1459, some c2364, some c2357, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7519 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7519 : lratChecker f7519 p7519 = .success := by decide +kernel
theorem unsat7519 : Unsatisfiable (PosFin 65) f7519 := by
  apply lratCheckerSound f7519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7519
  · intro a ha; simp [p7519] at ha; subst a; trivial
  · exact checked7519
theorem derived7519 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7519 := by
  apply localUnsat_implies_entails f7519 [c771, c775, c748, c755, c7517, c779, c774, c2299, c7518, c1459, c2364, c2357] c7519 unsat7519 (by rfl) a
  have h0 : Entails.eval a c771 := h 770 (by decide)
  have h1 : Entails.eval a c775 := h 774 (by decide)
  have h2 : Entails.eval a c748 := h 747 (by decide)
  have h3 : Entails.eval a c755 := h 754 (by decide)
  have h4 : Entails.eval a c7517 := derived7517 a h
  have h5 : Entails.eval a c779 := h 778 (by decide)
  have h6 : Entails.eval a c774 := h 773 (by decide)
  have h7 : Entails.eval a c2299 := h 2298 (by decide)
  have h8 : Entails.eval a c7518 := derived7518 a h
  have h9 : Entails.eval a c1459 := h 1458 (by decide)
  have h10 : Entails.eval a c2364 := h 2363 (by decide)
  have h11 : Entails.eval a c2357 := h 2356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7520 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7520 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1727, some c870, some c1940, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7520 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7520 : lratChecker f7520 p7520 = .success := by decide +kernel
theorem unsat7520 : Unsatisfiable (PosFin 65) f7520 := by
  apply lratCheckerSound f7520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7520
  · intro a ha; simp [p7520] at ha; subst a; trivial
  · exact checked7520
theorem derived7520 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7520 := by
  apply localUnsat_implies_entails f7520 [c1727, c870, c1940] c7520 unsat7520 (by rfl) a
  have h0 : Entails.eval a c1727 := h 1726 (by decide)
  have h1 : Entails.eval a c870 := h 869 (by decide)
  have h2 : Entails.eval a c1940 := h 1939 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7521 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7521 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7514, some c7513, some c755, some c7262, some c781, some c775, some c7502, some c771, some c7515, some c7508, some c7519, some c7450, some c748, some c763, some c760, some c774, some c7520, some c1677, some c888, some c1949, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7521 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7521 : lratChecker f7521 p7521 = .success := by decide +kernel
theorem unsat7521 : Unsatisfiable (PosFin 65) f7521 := by
  apply lratCheckerSound f7521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7521
  · intro a ha; simp [p7521] at ha; subst a; trivial
  · exact checked7521
theorem derived7521 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7521 := by
  apply localUnsat_implies_entails f7521 [c7514, c7513, c755, c7262, c781, c775, c7502, c771, c7515, c7508, c7519, c7450, c748, c763, c760, c774, c7520, c1677, c888, c1949] c7521 unsat7521 (by rfl) a
  have h0 : Entails.eval a c7514 := derived7514 a h
  have h1 : Entails.eval a c7513 := derived7513 a h
  have h2 : Entails.eval a c755 := h 754 (by decide)
  have h3 : Entails.eval a c7262 := derived7262 a h
  have h4 : Entails.eval a c781 := h 780 (by decide)
  have h5 : Entails.eval a c775 := h 774 (by decide)
  have h6 : Entails.eval a c7502 := derived7502 a h
  have h7 : Entails.eval a c771 := h 770 (by decide)
  have h8 : Entails.eval a c7515 := derived7515 a h
  have h9 : Entails.eval a c7508 := derived7508 a h
  have h10 : Entails.eval a c7519 := derived7519 a h
  have h11 : Entails.eval a c7450 := derived7450 a h
  have h12 : Entails.eval a c748 := h 747 (by decide)
  have h13 : Entails.eval a c763 := h 762 (by decide)
  have h14 : Entails.eval a c760 := h 759 (by decide)
  have h15 : Entails.eval a c774 := h 773 (by decide)
  have h16 : Entails.eval a c7520 := derived7520 a h
  have h17 : Entails.eval a c1677 := h 1676 (by decide)
  have h18 : Entails.eval a c888 := h 887 (by decide)
  have h19 : Entails.eval a c1949 := h 1948 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7522 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7522 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2364, some c2357, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7522 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7522 : lratChecker f7522 p7522 = .success := by decide +kernel
theorem unsat7522 : Unsatisfiable (PosFin 65) f7522 := by
  apply lratCheckerSound f7522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7522
  · intro a ha; simp [p7522] at ha; subst a; trivial
  · exact checked7522
theorem derived7522 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7522 := by
  apply localUnsat_implies_entails f7522 [c2364, c2357] c7522 unsat7522 (by rfl) a
  have h0 : Entails.eval a c2364 := h 2363 (by decide)
  have h1 : Entails.eval a c2357 := h 2356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7523 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7523 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7513, some c755, some c748, some c7262, some c781, some c775, some c771, some c7502, some c7515, some c7508, some c7521, some c779, some c774, some c2299, some c7522, some c1460, some c1457, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7523 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7523 : lratChecker f7523 p7523 = .success := by decide +kernel
theorem unsat7523 : Unsatisfiable (PosFin 65) f7523 := by
  apply lratCheckerSound f7523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7523
  · intro a ha; simp [p7523] at ha; subst a; trivial
  · exact checked7523
theorem derived7523 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7523 := by
  apply localUnsat_implies_entails f7523 [c7513, c755, c748, c7262, c781, c775, c771, c7502, c7515, c7508, c7521, c779, c774, c2299, c7522, c1460, c1457] c7523 unsat7523 (by rfl) a
  have h0 : Entails.eval a c7513 := derived7513 a h
  have h1 : Entails.eval a c755 := h 754 (by decide)
  have h2 : Entails.eval a c748 := h 747 (by decide)
  have h3 : Entails.eval a c7262 := derived7262 a h
  have h4 : Entails.eval a c781 := h 780 (by decide)
  have h5 : Entails.eval a c775 := h 774 (by decide)
  have h6 : Entails.eval a c771 := h 770 (by decide)
  have h7 : Entails.eval a c7502 := derived7502 a h
  have h8 : Entails.eval a c7515 := derived7515 a h
  have h9 : Entails.eval a c7508 := derived7508 a h
  have h10 : Entails.eval a c7521 := derived7521 a h
  have h11 : Entails.eval a c779 := h 778 (by decide)
  have h12 : Entails.eval a c774 := h 773 (by decide)
  have h13 : Entails.eval a c2299 := h 2298 (by decide)
  have h14 : Entails.eval a c7522 := derived7522 a h
  have h15 : Entails.eval a c1460 := h 1459 (by decide)
  have h16 : Entails.eval a c1457 := h 1456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7524 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7524 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7514, some c7523, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7524 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7524 : lratChecker f7524 p7524 = .success := by decide +kernel
theorem unsat7524 : Unsatisfiable (PosFin 65) f7524 := by
  apply lratCheckerSound f7524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7524
  · intro a ha; simp [p7524] at ha; subst a; trivial
  · exact checked7524
theorem derived7524 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7524 := by
  apply localUnsat_implies_entails f7524 [c7514, c7523] c7524 unsat7524 (by rfl) a
  have h0 : Entails.eval a c7514 := derived7514 a h
  have h1 : Entails.eval a c7523 := derived7523 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7525 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7525 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c383, some c1384, some c1056, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7525 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7525 : lratChecker f7525 p7525 = .success := by decide +kernel
theorem unsat7525 : Unsatisfiable (PosFin 65) f7525 := by
  apply lratCheckerSound f7525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7525
  · intro a ha; simp [p7525] at ha; subst a; trivial
  · exact checked7525
theorem derived7525 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7525 := by
  apply localUnsat_implies_entails f7525 [c383, c1384, c1056] c7525 unsat7525 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c1384 := h 1383 (by decide)
  have h2 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7526 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7526 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1113, some c1115, some c1135, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7526 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7526 : lratChecker f7526 p7526 = .success := by decide +kernel
theorem unsat7526 : Unsatisfiable (PosFin 65) f7526 := by
  apply lratCheckerSound f7526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7526
  · intro a ha; simp [p7526] at ha; subst a; trivial
  · exact checked7526
theorem derived7526 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7526 := by
  apply localUnsat_implies_entails f7526 [c1113, c1115, c1135] c7526 unsat7526 (by rfl) a
  have h0 : Entails.eval a c1113 := h 1112 (by decide)
  have h1 : Entails.eval a c1115 := h 1114 (by decide)
  have h2 : Entails.eval a c1135 := h 1134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7527 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7527 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1056, some c2539, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7527 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7527 : lratChecker f7527 p7527 = .success := by decide +kernel
theorem unsat7527 : Unsatisfiable (PosFin 65) f7527 := by
  apply lratCheckerSound f7527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7527
  · intro a ha; simp [p7527] at ha; subst a; trivial
  · exact checked7527
theorem derived7527 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7527 := by
  apply localUnsat_implies_entails f7527 [c1056, c2539] c7527 unsat7527 (by rfl) a
  have h0 : Entails.eval a c1056 := h 1055 (by decide)
  have h1 : Entails.eval a c2539 := h 2538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7528 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7528 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7503, some c810, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7528 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7528 : lratChecker f7528 p7528 = .success := by decide +kernel
theorem unsat7528 : Unsatisfiable (PosFin 65) f7528 := by
  apply lratCheckerSound f7528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7528
  · intro a ha; simp [p7528] at ha; subst a; trivial
  · exact checked7528
theorem derived7528 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7528 := by
  apply localUnsat_implies_entails f7528 [c7503, c810] c7528 unsat7528 (by rfl) a
  have h0 : Entails.eval a c7503 := derived7503 a h
  have h1 : Entails.eval a c810 := h 809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7529 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7529 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7524, some c7526, some c7527, some c7528, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7529 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7529 : lratChecker f7529 p7529 = .success := by decide +kernel
theorem unsat7529 : Unsatisfiable (PosFin 65) f7529 := by
  apply lratCheckerSound f7529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7529
  · intro a ha; simp [p7529] at ha; subst a; trivial
  · exact checked7529
theorem derived7529 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7529 := by
  apply localUnsat_implies_entails f7529 [c7524, c7526, c7527, c7528] c7529 unsat7529 (by rfl) a
  have h0 : Entails.eval a c7524 := derived7524 a h
  have h1 : Entails.eval a c7526 := derived7526 a h
  have h2 : Entails.eval a c7527 := derived7527 a h
  have h3 : Entails.eval a c7528 := derived7528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7530 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7530 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1782, some c1732, some c2535, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p7530 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7530 : lratChecker f7530 p7530 = .success := by decide +kernel
theorem unsat7530 : Unsatisfiable (PosFin 65) f7530 := by
  apply lratCheckerSound f7530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7530
  · intro a ha; simp [p7530] at ha; subst a; trivial
  · exact checked7530
theorem derived7530 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7530 := by
  apply localUnsat_implies_entails f7530 [c1782, c1732, c2535] c7530 unsat7530 (by rfl) a
  have h0 : Entails.eval a c1782 := h 1781 (by decide)
  have h1 : Entails.eval a c1732 := h 1731 (by decide)
  have h2 : Entails.eval a c2535 := h 2534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7531 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7531 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1241, some c1254, some c294, some c314, some c1221, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7531 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7531 : lratChecker f7531 p7531 = .success := by decide +kernel
theorem unsat7531 : Unsatisfiable (PosFin 65) f7531 := by
  apply lratCheckerSound f7531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7531
  · intro a ha; simp [p7531] at ha; subst a; trivial
  · exact checked7531
theorem derived7531 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7531 := by
  apply localUnsat_implies_entails f7531 [c1241, c1254, c294, c314, c1221] c7531 unsat7531 (by rfl) a
  have h0 : Entails.eval a c1241 := h 1240 (by decide)
  have h1 : Entails.eval a c1254 := h 1253 (by decide)
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c1221 := h 1220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7532 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7532 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1075, some c923, some c2237, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7532 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7532 : lratChecker f7532 p7532 = .success := by decide +kernel
theorem unsat7532 : Unsatisfiable (PosFin 65) f7532 := by
  apply lratCheckerSound f7532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7532
  · intro a ha; simp [p7532] at ha; subst a; trivial
  · exact checked7532
theorem derived7532 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7532 := by
  apply localUnsat_implies_entails f7532 [c1075, c923, c2237] c7532 unsat7532 (by rfl) a
  have h0 : Entails.eval a c1075 := h 1074 (by decide)
  have h1 : Entails.eval a c923 := h 922 (by decide)
  have h2 : Entails.eval a c2237 := h 2236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7533 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7533 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7530, some c7531, some c7485, some c7532, some c790, some c1133, some c2616, some c1120, some c1830, some c2544, some c1108, some c1080, some c1088, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7533 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7533 : lratChecker f7533 p7533 = .success := by decide +kernel
theorem unsat7533 : Unsatisfiable (PosFin 65) f7533 := by
  apply lratCheckerSound f7533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7533
  · intro a ha; simp [p7533] at ha; subst a; trivial
  · exact checked7533
theorem derived7533 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7533 := by
  apply localUnsat_implies_entails f7533 [c7530, c7531, c7485, c7532, c790, c1133, c2616, c1120, c1830, c2544, c1108, c1080, c1088] c7533 unsat7533 (by rfl) a
  have h0 : Entails.eval a c7530 := derived7530 a h
  have h1 : Entails.eval a c7531 := derived7531 a h
  have h2 : Entails.eval a c7485 := derived7485 a h
  have h3 : Entails.eval a c7532 := derived7532 a h
  have h4 : Entails.eval a c790 := h 789 (by decide)
  have h5 : Entails.eval a c1133 := h 1132 (by decide)
  have h6 : Entails.eval a c2616 := h 2615 (by decide)
  have h7 : Entails.eval a c1120 := h 1119 (by decide)
  have h8 : Entails.eval a c1830 := h 1829 (by decide)
  have h9 : Entails.eval a c2544 := h 2543 (by decide)
  have h10 : Entails.eval a c1108 := h 1107 (by decide)
  have h11 : Entails.eval a c1080 := h 1079 (by decide)
  have h12 : Entails.eval a c1088 := h 1087 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7534 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7534 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7289, some c316, some c320, some c307, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7534 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7534 : lratChecker f7534 p7534 = .success := by decide +kernel
theorem unsat7534 : Unsatisfiable (PosFin 65) f7534 := by
  apply lratCheckerSound f7534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7534
  · intro a ha; simp [p7534] at ha; subst a; trivial
  · exact checked7534
theorem derived7534 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7534 := by
  apply localUnsat_implies_entails f7534 [c7289, c316, c320, c307] c7534 unsat7534 (by rfl) a
  have h0 : Entails.eval a c7289 := derived7289 a h
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7535 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7535 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c815, some c1139, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7535 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7535 : lratChecker f7535 p7535 = .success := by decide +kernel
theorem unsat7535 : Unsatisfiable (PosFin 65) f7535 := by
  apply lratCheckerSound f7535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7535
  · intro a ha; simp [p7535] at ha; subst a; trivial
  · exact checked7535
theorem derived7535 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7535 := by
  apply localUnsat_implies_entails f7535 [c815, c1139] c7535 unsat7535 (by rfl) a
  have h0 : Entails.eval a c815 := h 814 (by decide)
  have h1 : Entails.eval a c1139 := h 1138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7536 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7536 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c798, some c967, some c1053, some c2038, some c2019, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7536 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7536 : lratChecker f7536 p7536 = .success := by decide +kernel
theorem unsat7536 : Unsatisfiable (PosFin 65) f7536 := by
  apply lratCheckerSound f7536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7536
  · intro a ha; simp [p7536] at ha; subst a; trivial
  · exact checked7536
theorem derived7536 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7536 := by
  apply localUnsat_implies_entails f7536 [c798, c967, c1053, c2038, c2019] c7536 unsat7536 (by rfl) a
  have h0 : Entails.eval a c798 := h 797 (by decide)
  have h1 : Entails.eval a c967 := h 966 (by decide)
  have h2 : Entails.eval a c1053 := h 1052 (by decide)
  have h3 : Entails.eval a c2038 := h 2037 (by decide)
  have h4 : Entails.eval a c2019 := h 2018 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7537 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7537 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1141, some c1134, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7537 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7537 : lratChecker f7537 p7537 = .success := by decide +kernel
theorem unsat7537 : Unsatisfiable (PosFin 65) f7537 := by
  apply lratCheckerSound f7537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7537
  · intro a ha; simp [p7537] at ha; subst a; trivial
  · exact checked7537
theorem derived7537 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7537 := by
  apply localUnsat_implies_entails f7537 [c1141, c1134] c7537 unsat7537 (by rfl) a
  have h0 : Entails.eval a c1141 := h 1140 (by decide)
  have h1 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7538 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7538 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7524, some c7529, some c7533, some c7534, some c7535, some c7537, some c7528, some c7536, some c7532, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7538 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7538 : lratChecker f7538 p7538 = .success := by decide +kernel
theorem unsat7538 : Unsatisfiable (PosFin 65) f7538 := by
  apply lratCheckerSound f7538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7538
  · intro a ha; simp [p7538] at ha; subst a; trivial
  · exact checked7538
theorem derived7538 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7538 := by
  apply localUnsat_implies_entails f7538 [c7524, c7529, c7533, c7534, c7535, c7537, c7528, c7536, c7532] c7538 unsat7538 (by rfl) a
  have h0 : Entails.eval a c7524 := derived7524 a h
  have h1 : Entails.eval a c7529 := derived7529 a h
  have h2 : Entails.eval a c7533 := derived7533 a h
  have h3 : Entails.eval a c7534 := derived7534 a h
  have h4 : Entails.eval a c7535 := derived7535 a h
  have h5 : Entails.eval a c7537 := derived7537 a h
  have h6 : Entails.eval a c7528 := derived7528 a h
  have h7 : Entails.eval a c7536 := derived7536 a h
  have h8 : Entails.eval a c7532 := derived7532 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7539 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7539 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7538, some c7524, some c7526, some c793, some c815, some c807, some c811, some c1054, some c2536, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7539 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7539 : lratChecker f7539 p7539 = .success := by decide +kernel
theorem unsat7539 : Unsatisfiable (PosFin 65) f7539 := by
  apply lratCheckerSound f7539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7539
  · intro a ha; simp [p7539] at ha; subst a; trivial
  · exact checked7539
theorem derived7539 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7539 := by
  apply localUnsat_implies_entails f7539 [c7538, c7524, c7526, c793, c815, c807, c811, c1054, c2536] c7539 unsat7539 (by rfl) a
  have h0 : Entails.eval a c7538 := derived7538 a h
  have h1 : Entails.eval a c7524 := derived7524 a h
  have h2 : Entails.eval a c7526 := derived7526 a h
  have h3 : Entails.eval a c793 := h 792 (by decide)
  have h4 : Entails.eval a c815 := h 814 (by decide)
  have h5 : Entails.eval a c807 := h 806 (by decide)
  have h6 : Entails.eval a c811 := h 810 (by decide)
  have h7 : Entails.eval a c1054 := h 1053 (by decide)
  have h8 : Entails.eval a c2536 := h 2535 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7540 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7540 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7539, some c7538, some c7524, some c793, some c7439, some c1142, some c2616, some c1143, some c1830, some c2544, some c1816, some c1140, some c1082, some c1137, some c1238, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7540 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7540 : lratChecker f7540 p7540 = .success := by decide +kernel
theorem unsat7540 : Unsatisfiable (PosFin 65) f7540 := by
  apply lratCheckerSound f7540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7540
  · intro a ha; simp [p7540] at ha; subst a; trivial
  · exact checked7540
theorem derived7540 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7540 := by
  apply localUnsat_implies_entails f7540 [c7539, c7538, c7524, c793, c7439, c1142, c2616, c1143, c1830, c2544, c1816, c1140, c1082, c1137, c1238] c7540 unsat7540 (by rfl) a
  have h0 : Entails.eval a c7539 := derived7539 a h
  have h1 : Entails.eval a c7538 := derived7538 a h
  have h2 : Entails.eval a c7524 := derived7524 a h
  have h3 : Entails.eval a c793 := h 792 (by decide)
  have h4 : Entails.eval a c7439 := derived7439 a h
  have h5 : Entails.eval a c1142 := h 1141 (by decide)
  have h6 : Entails.eval a c2616 := h 2615 (by decide)
  have h7 : Entails.eval a c1143 := h 1142 (by decide)
  have h8 : Entails.eval a c1830 := h 1829 (by decide)
  have h9 : Entails.eval a c2544 := h 2543 (by decide)
  have h10 : Entails.eval a c1816 := h 1815 (by decide)
  have h11 : Entails.eval a c1140 := h 1139 (by decide)
  have h12 : Entails.eval a c1082 := h 1081 (by decide)
  have h13 : Entails.eval a c1137 := h 1136 (by decide)
  have h14 : Entails.eval a c1238 := h 1237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7541 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7541 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c743, some c1460, some c927, some c2380, some c7509, some c1237, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7541 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7541 : lratChecker f7541 p7541 = .success := by decide +kernel
theorem unsat7541 : Unsatisfiable (PosFin 65) f7541 := by
  apply lratCheckerSound f7541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7541
  · intro a ha; simp [p7541] at ha; subst a; trivial
  · exact checked7541
theorem derived7541 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7541 := by
  apply localUnsat_implies_entails f7541 [c743, c1460, c927, c2380, c7509, c1237] c7541 unsat7541 (by rfl) a
  have h0 : Entails.eval a c743 := h 742 (by decide)
  have h1 : Entails.eval a c1460 := h 1459 (by decide)
  have h2 : Entails.eval a c927 := h 926 (by decide)
  have h3 : Entails.eval a c2380 := h 2379 (by decide)
  have h4 : Entails.eval a c7509 := derived7509 a h
  have h5 : Entails.eval a c1237 := h 1236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7542 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7542 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c738, some c1314, some c888, some c1078, some c1949, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7542 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7542 : lratChecker f7542 p7542 = .success := by decide +kernel
theorem unsat7542 : Unsatisfiable (PosFin 65) f7542 := by
  apply lratCheckerSound f7542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7542
  · intro a ha; simp [p7542] at ha; subst a; trivial
  · exact checked7542
theorem derived7542 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7542 := by
  apply localUnsat_implies_entails f7542 [c738, c1314, c888, c1078, c1949] c7542 unsat7542 (by rfl) a
  have h0 : Entails.eval a c738 := h 737 (by decide)
  have h1 : Entails.eval a c1314 := h 1313 (by decide)
  have h2 : Entails.eval a c888 := h 887 (by decide)
  have h3 : Entails.eval a c1078 := h 1077 (by decide)
  have h4 : Entails.eval a c1949 := h 1948 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7543 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7543 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7524, some c7538, some c7540, some c7534, some c7535, some c7537, some c816, some c787, some c807, some c801, some c809, some c7542, some c743, some c1460, some c927, some c878, some c2380, some c2112, some c1237, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7543 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked7543 : lratChecker f7543 p7543 = .success := by decide +kernel
theorem unsat7543 : Unsatisfiable (PosFin 65) f7543 := by
  apply lratCheckerSound f7543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7543
  · intro a ha; simp [p7543] at ha; subst a; trivial
  · exact checked7543
theorem derived7543 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7543 := by
  apply localUnsat_implies_entails f7543 [c7524, c7538, c7540, c7534, c7535, c7537, c816, c787, c807, c801, c809, c7542, c743, c1460, c927, c878, c2380, c2112, c1237] c7543 unsat7543 (by rfl) a
  have h0 : Entails.eval a c7524 := derived7524 a h
  have h1 : Entails.eval a c7538 := derived7538 a h
  have h2 : Entails.eval a c7540 := derived7540 a h
  have h3 : Entails.eval a c7534 := derived7534 a h
  have h4 : Entails.eval a c7535 := derived7535 a h
  have h5 : Entails.eval a c7537 := derived7537 a h
  have h6 : Entails.eval a c816 := h 815 (by decide)
  have h7 : Entails.eval a c787 := h 786 (by decide)
  have h8 : Entails.eval a c807 := h 806 (by decide)
  have h9 : Entails.eval a c801 := h 800 (by decide)
  have h10 : Entails.eval a c809 := h 808 (by decide)
  have h11 : Entails.eval a c7542 := derived7542 a h
  have h12 : Entails.eval a c743 := h 742 (by decide)
  have h13 : Entails.eval a c1460 := h 1459 (by decide)
  have h14 : Entails.eval a c927 := h 926 (by decide)
  have h15 : Entails.eval a c878 := h 877 (by decide)
  have h16 : Entails.eval a c2380 := h 2379 (by decide)
  have h17 : Entails.eval a c2112 := h 2111 (by decide)
  have h18 : Entails.eval a c1237 := h 1236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7544 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7544 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c296, some c7295, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7544 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7544 : lratChecker f7544 p7544 = .success := by decide +kernel
theorem unsat7544 : Unsatisfiable (PosFin 65) f7544 := by
  apply lratCheckerSound f7544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7544
  · intro a ha; simp [p7544] at ha; subst a; trivial
  · exact checked7544
theorem derived7544 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7544 := by
  apply localUnsat_implies_entails f7544 [c296, c7295] c7544 unsat7544 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c7295 := derived7295 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7545 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7545 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7544, some c7301, some c1134, some c1135, some c1143, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7545 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7545 : lratChecker f7545 p7545 = .success := by decide +kernel
theorem unsat7545 : Unsatisfiable (PosFin 65) f7545 := by
  apply lratCheckerSound f7545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7545
  · intro a ha; simp [p7545] at ha; subst a; trivial
  · exact checked7545
theorem derived7545 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7545 := by
  apply localUnsat_implies_entails f7545 [c7544, c7301, c1134, c1135, c1143] c7545 unsat7545 (by rfl) a
  have h0 : Entails.eval a c7544 := derived7544 a h
  have h1 : Entails.eval a c7301 := derived7301 a h
  have h2 : Entails.eval a c1134 := h 1133 (by decide)
  have h3 : Entails.eval a c1135 := h 1134 (by decide)
  have h4 : Entails.eval a c1143 := h 1142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7546 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7546 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7543, some c7524, some c792, some c7425, some c2624, some c1821, some c1147, some c1154, some c1163, some c1839, some c1108, some c1137, some c1158, some c1225, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7546 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7546 : lratChecker f7546 p7546 = .success := by decide +kernel
theorem unsat7546 : Unsatisfiable (PosFin 65) f7546 := by
  apply lratCheckerSound f7546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7546
  · intro a ha; simp [p7546] at ha; subst a; trivial
  · exact checked7546
theorem derived7546 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7546 := by
  apply localUnsat_implies_entails f7546 [c7543, c7524, c792, c7425, c2624, c1821, c1147, c1154, c1163, c1839, c1108, c1137, c1158, c1225] c7546 unsat7546 (by rfl) a
  have h0 : Entails.eval a c7543 := derived7543 a h
  have h1 : Entails.eval a c7524 := derived7524 a h
  have h2 : Entails.eval a c792 := h 791 (by decide)
  have h3 : Entails.eval a c7425 := derived7425 a h
  have h4 : Entails.eval a c2624 := h 2623 (by decide)
  have h5 : Entails.eval a c1821 := h 1820 (by decide)
  have h6 : Entails.eval a c1147 := h 1146 (by decide)
  have h7 : Entails.eval a c1154 := h 1153 (by decide)
  have h8 : Entails.eval a c1163 := h 1162 (by decide)
  have h9 : Entails.eval a c1839 := h 1838 (by decide)
  have h10 : Entails.eval a c1108 := h 1107 (by decide)
  have h11 : Entails.eval a c1137 := h 1136 (by decide)
  have h12 : Entails.eval a c1158 := h 1157 (by decide)
  have h13 : Entails.eval a c1225 := h 1224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7547 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7547 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c794, some c811, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7547 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7547 : lratChecker f7547 p7547 = .success := by decide +kernel
theorem unsat7547 : Unsatisfiable (PosFin 65) f7547 := by
  apply lratCheckerSound f7547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7547
  · intro a ha; simp [p7547] at ha; subst a; trivial
  · exact checked7547
theorem derived7547 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7547 := by
  apply localUnsat_implies_entails f7547 [c794, c811] c7547 unsat7547 (by rfl) a
  have h0 : Entails.eval a c794 := h 793 (by decide)
  have h1 : Entails.eval a c811 := h 810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7548 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7548 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7543, some c7524, some c7547, some c1135, some c1134, some c1143, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7548 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7548 : lratChecker f7548 p7548 = .success := by decide +kernel
theorem unsat7548 : Unsatisfiable (PosFin 65) f7548 := by
  apply lratCheckerSound f7548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7548
  · intro a ha; simp [p7548] at ha; subst a; trivial
  · exact checked7548
theorem derived7548 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7548 := by
  apply localUnsat_implies_entails f7548 [c7543, c7524, c7547, c1135, c1134, c1143] c7548 unsat7548 (by rfl) a
  have h0 : Entails.eval a c7543 := derived7543 a h
  have h1 : Entails.eval a c7524 := derived7524 a h
  have h2 : Entails.eval a c7547 := derived7547 a h
  have h3 : Entails.eval a c1135 := h 1134 (by decide)
  have h4 : Entails.eval a c1134 := h 1133 (by decide)
  have h5 : Entails.eval a c1143 := h 1142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7549 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7549 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7524, some c7543, some c7548, some c792, some c7535, some c7546, some c1113, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7549 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7549 : lratChecker f7549 p7549 = .success := by decide +kernel
theorem unsat7549 : Unsatisfiable (PosFin 65) f7549 := by
  apply lratCheckerSound f7549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7549
  · intro a ha; simp [p7549] at ha; subst a; trivial
  · exact checked7549
theorem derived7549 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7549 := by
  apply localUnsat_implies_entails f7549 [c7524, c7543, c7548, c792, c7535, c7546, c1113] c7549 unsat7549 (by rfl) a
  have h0 : Entails.eval a c7524 := derived7524 a h
  have h1 : Entails.eval a c7543 := derived7543 a h
  have h2 : Entails.eval a c7548 := derived7548 a h
  have h3 : Entails.eval a c792 := h 791 (by decide)
  have h4 : Entails.eval a c7535 := derived7535 a h
  have h5 : Entails.eval a c7546 := derived7546 a h
  have h6 : Entails.eval a c1113 := h 1112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7550 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7550 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7497, some c7549, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7550 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7550 : lratChecker f7550 p7550 = .success := by decide +kernel
theorem unsat7550 : Unsatisfiable (PosFin 65) f7550 := by
  apply lratCheckerSound f7550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7550
  · intro a ha; simp [p7550] at ha; subst a; trivial
  · exact checked7550
theorem derived7550 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7550 := by
  apply localUnsat_implies_entails f7550 [c7470, c7497, c7549] c7550 unsat7550 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7497 := derived7497 a h
  have h2 : Entails.eval a c7549 := derived7549 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7551 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c335, some c7488, some c1613, some c7272, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7551 : lratChecker f7551 p7551 = .success := by decide +kernel
theorem unsat7551 : Unsatisfiable (PosFin 65) f7551 := by
  apply lratCheckerSound f7551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7551
  · intro a ha; simp [p7551] at ha; subst a; trivial
  · exact checked7551
theorem derived7551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7551 := by
  apply localUnsat_implies_entails f7551 [c335, c7488, c1613, c7272] c7551 unsat7551 (by rfl) a
  have h0 : Entails.eval a c335 := h 334 (by decide)
  have h1 : Entails.eval a c7488 := derived7488 a h
  have h2 : Entails.eval a c1613 := h 1612 (by decide)
  have h3 : Entails.eval a c7272 := derived7272 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7552 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7551, some c7340, some c1414, some c2059, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7552 : lratChecker f7552 p7552 = .success := by decide +kernel
theorem unsat7552 : Unsatisfiable (PosFin 65) f7552 := by
  apply lratCheckerSound f7552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7552
  · intro a ha; simp [p7552] at ha; subst a; trivial
  · exact checked7552
theorem derived7552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7552 := by
  apply localUnsat_implies_entails f7552 [c7551, c7340, c1414, c2059] c7552 unsat7552 (by rfl) a
  have h0 : Entails.eval a c7551 := derived7551 a h
  have h1 : Entails.eval a c7340 := derived7340 a h
  have h2 : Entails.eval a c1414 := h 1413 (by decide)
  have h3 : Entails.eval a c2059 := h 2058 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7553 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7552, some c1145, some c1469, some c2583, some c1414, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7553 : lratChecker f7553 p7553 = .success := by decide +kernel
theorem unsat7553 : Unsatisfiable (PosFin 65) f7553 := by
  apply lratCheckerSound f7553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7553
  · intro a ha; simp [p7553] at ha; subst a; trivial
  · exact checked7553
theorem derived7553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7553 := by
  apply localUnsat_implies_entails f7553 [c7552, c1145, c1469, c2583, c1414] c7553 unsat7553 (by rfl) a
  have h0 : Entails.eval a c7552 := derived7552 a h
  have h1 : Entails.eval a c1145 := h 1144 (by decide)
  have h2 : Entails.eval a c1469 := h 1468 (by decide)
  have h3 : Entails.eval a c2583 := h 2582 (by decide)
  have h4 : Entails.eval a c1414 := h 1413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7554 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c359, some c1466, some c1502, some c1221, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7554 : lratChecker f7554 p7554 = .success := by decide +kernel
theorem unsat7554 : Unsatisfiable (PosFin 65) f7554 := by
  apply lratCheckerSound f7554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7554
  · intro a ha; simp [p7554] at ha; subst a; trivial
  · exact checked7554
theorem derived7554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7554 := by
  apply localUnsat_implies_entails f7554 [c359, c1466, c1502, c1221] c7554 unsat7554 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c1466 := h 1465 (by decide)
  have h2 : Entails.eval a c1502 := h 1501 (by decide)
  have h3 : Entails.eval a c1221 := h 1220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7555 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2101, some c2018, some c1092, some c1081, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7555 : lratChecker f7555 p7555 = .success := by decide +kernel
theorem unsat7555 : Unsatisfiable (PosFin 65) f7555 := by
  apply lratCheckerSound f7555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7555
  · intro a ha; simp [p7555] at ha; subst a; trivial
  · exact checked7555
theorem derived7555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7555 := by
  apply localUnsat_implies_entails f7555 [c2101, c2018, c1092, c1081] c7555 unsat7555 (by rfl) a
  have h0 : Entails.eval a c2101 := h 2100 (by decide)
  have h1 : Entails.eval a c2018 := h 2017 (by decide)
  have h2 : Entails.eval a c1092 := h 1091 (by decide)
  have h3 : Entails.eval a c1081 := h 1080 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7556 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7553, some c7554, some c7340, some c1341, some c1889, some c2417, some c1021, some c1022, some c931, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7556 : lratChecker f7556 p7556 = .success := by decide +kernel
theorem unsat7556 : Unsatisfiable (PosFin 65) f7556 := by
  apply lratCheckerSound f7556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7556
  · intro a ha; simp [p7556] at ha; subst a; trivial
  · exact checked7556
theorem derived7556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7556 := by
  apply localUnsat_implies_entails f7556 [c7553, c7554, c7340, c1341, c1889, c2417, c1021, c1022, c931] c7556 unsat7556 (by rfl) a
  have h0 : Entails.eval a c7553 := derived7553 a h
  have h1 : Entails.eval a c7554 := derived7554 a h
  have h2 : Entails.eval a c7340 := derived7340 a h
  have h3 : Entails.eval a c1341 := h 1340 (by decide)
  have h4 : Entails.eval a c1889 := h 1888 (by decide)
  have h5 : Entails.eval a c2417 := h 2416 (by decide)
  have h6 : Entails.eval a c1021 := h 1020 (by decide)
  have h7 : Entails.eval a c1022 := h 1021 (by decide)
  have h8 : Entails.eval a c931 := h 930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7557 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1414, some c2406, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7557 : lratChecker f7557 p7557 = .success := by decide +kernel
theorem unsat7557 : Unsatisfiable (PosFin 65) f7557 := by
  apply lratCheckerSound f7557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7557
  · intro a ha; simp [p7557] at ha; subst a; trivial
  · exact checked7557
theorem derived7557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7557 := by
  apply localUnsat_implies_entails f7557 [c1414, c2406] c7557 unsat7557 (by rfl) a
  have h0 : Entails.eval a c1414 := h 1413 (by decide)
  have h1 : Entails.eval a c2406 := h 2405 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7558 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7556, some c358, some c1295, some c1363, some c7557, some c7130, some c929, some c1304, some c1961, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p7558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7558 : lratChecker f7558 p7558 = .success := by decide +kernel
theorem unsat7558 : Unsatisfiable (PosFin 65) f7558 := by
  apply lratCheckerSound f7558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7558
  · intro a ha; simp [p7558] at ha; subst a; trivial
  · exact checked7558
theorem derived7558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7558 := by
  apply localUnsat_implies_entails f7558 [c7556, c358, c1295, c1363, c7557, c7130, c929, c1304, c1961] c7558 unsat7558 (by rfl) a
  have h0 : Entails.eval a c7556 := derived7556 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c1295 := h 1294 (by decide)
  have h3 : Entails.eval a c1363 := h 1362 (by decide)
  have h4 : Entails.eval a c7557 := derived7557 a h
  have h5 : Entails.eval a c7130 := derived7130 a h
  have h6 : Entails.eval a c929 := h 928 (by decide)
  have h7 : Entails.eval a c1304 := h 1303 (by decide)
  have h8 : Entails.eval a c1961 := h 1960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7559 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1287, some c1352, some c2193, some c1992, some c1028, some c1026, some c919, some c1312, some c701, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7559 : lratChecker f7559 p7559 = .success := by decide +kernel
theorem unsat7559 : Unsatisfiable (PosFin 65) f7559 := by
  apply lratCheckerSound f7559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7559
  · intro a ha; simp [p7559] at ha; subst a; trivial
  · exact checked7559
theorem derived7559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7559 := by
  apply localUnsat_implies_entails f7559 [c1287, c1352, c2193, c1992, c1028, c1026, c919, c1312, c701] c7559 unsat7559 (by rfl) a
  have h0 : Entails.eval a c1287 := h 1286 (by decide)
  have h1 : Entails.eval a c1352 := h 1351 (by decide)
  have h2 : Entails.eval a c2193 := h 2192 (by decide)
  have h3 : Entails.eval a c1992 := h 1991 (by decide)
  have h4 : Entails.eval a c1028 := h 1027 (by decide)
  have h5 : Entails.eval a c1026 := h 1025 (by decide)
  have h6 : Entails.eval a c919 := h 918 (by decide)
  have h7 : Entails.eval a c1312 := h 1311 (by decide)
  have h8 : Entails.eval a c701 := h 700 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7560 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1415, some c2407, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7560 : lratChecker f7560 p7560 = .success := by decide +kernel
theorem unsat7560 : Unsatisfiable (PosFin 65) f7560 := by
  apply lratCheckerSound f7560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7560
  · intro a ha; simp [p7560] at ha; subst a; trivial
  · exact checked7560
theorem derived7560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7560 := by
  apply localUnsat_implies_entails f7560 [c1415, c2407] c7560 unsat7560 (by rfl) a
  have h0 : Entails.eval a c1415 := h 1414 (by decide)
  have h1 : Entails.eval a c2407 := h 2406 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7561 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7558, some c7231, some c7559, some c1295, some c1363, some c7560, some c7130, some c925, some c929, some c927, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p7561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7561 : lratChecker f7561 p7561 = .success := by decide +kernel
theorem unsat7561 : Unsatisfiable (PosFin 65) f7561 := by
  apply lratCheckerSound f7561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7561
  · intro a ha; simp [p7561] at ha; subst a; trivial
  · exact checked7561
theorem derived7561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7561 := by
  apply localUnsat_implies_entails f7561 [c7558, c7231, c7559, c1295, c1363, c7560, c7130, c925, c929, c927] c7561 unsat7561 (by rfl) a
  have h0 : Entails.eval a c7558 := derived7558 a h
  have h1 : Entails.eval a c7231 := derived7231 a h
  have h2 : Entails.eval a c7559 := derived7559 a h
  have h3 : Entails.eval a c1295 := h 1294 (by decide)
  have h4 : Entails.eval a c1363 := h 1362 (by decide)
  have h5 : Entails.eval a c7560 := derived7560 a h
  have h6 : Entails.eval a c7130 := derived7130 a h
  have h7 : Entails.eval a c925 := h 924 (by decide)
  have h8 : Entails.eval a c929 := h 928 (by decide)
  have h9 : Entails.eval a c927 := h 926 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7562 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c968, some c1055, some c1110, some c2021, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7562 : lratChecker f7562 p7562 = .success := by decide +kernel
theorem unsat7562 : Unsatisfiable (PosFin 65) f7562 := by
  apply lratCheckerSound f7562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7562
  · intro a ha; simp [p7562] at ha; subst a; trivial
  · exact checked7562
theorem derived7562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7562 := by
  apply localUnsat_implies_entails f7562 [c968, c1055, c1110, c2021] c7562 unsat7562 (by rfl) a
  have h0 : Entails.eval a c968 := h 967 (by decide)
  have h1 : Entails.eval a c1055 := h 1054 (by decide)
  have h2 : Entails.eval a c1110 := h 1109 (by decide)
  have h3 : Entails.eval a c2021 := h 2020 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7563 : DefaultClause 65 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1782, some c1566, some c7555, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7563 : lratChecker f7563 p7563 = .success := by decide +kernel
theorem unsat7563 : Unsatisfiable (PosFin 65) f7563 := by
  apply lratCheckerSound f7563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7563
  · intro a ha; simp [p7563] at ha; subst a; trivial
  · exact checked7563
theorem derived7563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7563 := by
  apply localUnsat_implies_entails f7563 [c1782, c1566, c7555] c7563 unsat7563 (by rfl) a
  have h0 : Entails.eval a c1782 := h 1781 (by decide)
  have h1 : Entails.eval a c1566 := h 1565 (by decide)
  have h2 : Entails.eval a c7555 := derived7555 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7564 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7561, some c7562, some c7563, some c7488, some c7340, some c1341, some c1889, some c1981, some c1323, some c2670, some c1816, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7564 : lratChecker f7564 p7564 = .success := by decide +kernel
theorem unsat7564 : Unsatisfiable (PosFin 65) f7564 := by
  apply lratCheckerSound f7564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7564
  · intro a ha; simp [p7564] at ha; subst a; trivial
  · exact checked7564
theorem derived7564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7564 := by
  apply localUnsat_implies_entails f7564 [c7561, c7562, c7563, c7488, c7340, c1341, c1889, c1981, c1323, c2670, c1816] c7564 unsat7564 (by rfl) a
  have h0 : Entails.eval a c7561 := derived7561 a h
  have h1 : Entails.eval a c7562 := derived7562 a h
  have h2 : Entails.eval a c7563 := derived7563 a h
  have h3 : Entails.eval a c7488 := derived7488 a h
  have h4 : Entails.eval a c7340 := derived7340 a h
  have h5 : Entails.eval a c1341 := h 1340 (by decide)
  have h6 : Entails.eval a c1889 := h 1888 (by decide)
  have h7 : Entails.eval a c1981 := h 1980 (by decide)
  have h8 : Entails.eval a c1323 := h 1322 (by decide)
  have h9 : Entails.eval a c2670 := h 2669 (by decide)
  have h10 : Entails.eval a c1816 := h 1815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7565 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c980, some c1072, some c1136, some c2035, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p7565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7565 : lratChecker f7565 p7565 = .success := by decide +kernel
theorem unsat7565 : Unsatisfiable (PosFin 65) f7565 := by
  apply lratCheckerSound f7565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7565
  · intro a ha; simp [p7565] at ha; subst a; trivial
  · exact checked7565
theorem derived7565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7565 := by
  apply localUnsat_implies_entails f7565 [c980, c1072, c1136, c2035] c7565 unsat7565 (by rfl) a
  have h0 : Entails.eval a c980 := h 979 (by decide)
  have h1 : Entails.eval a c1072 := h 1071 (by decide)
  have h2 : Entails.eval a c1136 := h 1135 (by decide)
  have h3 : Entails.eval a c2035 := h 2034 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7566 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7561, some c7565, some c7564, some c7439, some c297, some c1287, some c1352, some c1992, some c1900, some c2679, some c1028, some c1855, some c907, some c1555, some c1816, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7566 : lratChecker f7566 p7566 = .success := by decide +kernel
theorem unsat7566 : Unsatisfiable (PosFin 65) f7566 := by
  apply lratCheckerSound f7566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7566
  · intro a ha; simp [p7566] at ha; subst a; trivial
  · exact checked7566
theorem derived7566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7566 := by
  apply localUnsat_implies_entails f7566 [c7561, c7565, c7564, c7439, c297, c1287, c1352, c1992, c1900, c2679, c1028, c1855, c907, c1555, c1816] c7566 unsat7566 (by rfl) a
  have h0 : Entails.eval a c7561 := derived7561 a h
  have h1 : Entails.eval a c7565 := derived7565 a h
  have h2 : Entails.eval a c7564 := derived7564 a h
  have h3 : Entails.eval a c7439 := derived7439 a h
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c1287 := h 1286 (by decide)
  have h6 : Entails.eval a c1352 := h 1351 (by decide)
  have h7 : Entails.eval a c1992 := h 1991 (by decide)
  have h8 : Entails.eval a c1900 := h 1899 (by decide)
  have h9 : Entails.eval a c2679 := h 2678 (by decide)
  have h10 : Entails.eval a c1028 := h 1027 (by decide)
  have h11 : Entails.eval a c1855 := h 1854 (by decide)
  have h12 : Entails.eval a c907 := h 906 (by decide)
  have h13 : Entails.eval a c1555 := h 1554 (by decide)
  have h14 : Entails.eval a c1816 := h 1815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7567 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7362, some c334, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7567 : lratChecker f7567 p7567 = .success := by decide +kernel
theorem unsat7567 : Unsatisfiable (PosFin 65) f7567 := by
  apply lratCheckerSound f7567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7567
  · intro a ha; simp [p7567] at ha; subst a; trivial
  · exact checked7567
theorem derived7567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7567 := by
  apply localUnsat_implies_entails f7567 [c7362, c334] c7567 unsat7567 (by rfl) a
  have h0 : Entails.eval a c7362 := derived7362 a h
  have h1 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7568 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1284, some c1350, some c1423, some c1966, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7568 : lratChecker f7568 p7568 = .success := by decide +kernel
theorem unsat7568 : Unsatisfiable (PosFin 65) f7568 := by
  apply lratCheckerSound f7568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7568
  · intro a ha; simp [p7568] at ha; subst a; trivial
  · exact checked7568
theorem derived7568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7568 := by
  apply localUnsat_implies_entails f7568 [c1284, c1350, c1423, c1966] c7568 unsat7568 (by rfl) a
  have h0 : Entails.eval a c1284 := h 1283 (by decide)
  have h1 : Entails.eval a c1350 := h 1349 (by decide)
  have h2 : Entails.eval a c1423 := h 1422 (by decide)
  have h3 : Entails.eval a c1966 := h 1965 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7569 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7566, some c7567, some c7375, some c293, some c7568, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7569 : lratChecker f7569 p7569 = .success := by decide +kernel
theorem unsat7569 : Unsatisfiable (PosFin 65) f7569 := by
  apply lratCheckerSound f7569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7569
  · intro a ha; simp [p7569] at ha; subst a; trivial
  · exact checked7569
theorem derived7569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7569 := by
  apply localUnsat_implies_entails f7569 [c7566, c7567, c7375, c293, c7568] c7569 unsat7569 (by rfl) a
  have h0 : Entails.eval a c7566 := derived7566 a h
  have h1 : Entails.eval a c7567 := derived7567 a h
  have h2 : Entails.eval a c7375 := derived7375 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c7568 := derived7568 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7570 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1470, some c1507, some c1220, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7570 : lratChecker f7570 p7570 = .success := by decide +kernel
theorem unsat7570 : Unsatisfiable (PosFin 65) f7570 := by
  apply lratCheckerSound f7570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7570
  · intro a ha; simp [p7570] at ha; subst a; trivial
  · exact checked7570
theorem derived7570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7570 := by
  apply localUnsat_implies_entails f7570 [c1470, c1507, c1220] c7570 unsat7570 (by rfl) a
  have h0 : Entails.eval a c1470 := h 1469 (by decide)
  have h1 : Entails.eval a c1507 := h 1506 (by decide)
  have h2 : Entails.eval a c1220 := h 1219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7571 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7569, some c7534, some c335, some c337, some c7570, some c1466, some c1502, some c2670, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7571 : lratChecker f7571 p7571 = .success := by decide +kernel
theorem unsat7571 : Unsatisfiable (PosFin 65) f7571 := by
  apply lratCheckerSound f7571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7571
  · intro a ha; simp [p7571] at ha; subst a; trivial
  · exact checked7571
theorem derived7571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7571 := by
  apply localUnsat_implies_entails f7571 [c7569, c7534, c335, c337, c7570, c1466, c1502, c2670] c7571 unsat7571 (by rfl) a
  have h0 : Entails.eval a c7569 := derived7569 a h
  have h1 : Entails.eval a c7534 := derived7534 a h
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c337 := h 336 (by decide)
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c1466 := h 1465 (by decide)
  have h6 : Entails.eval a c1502 := h 1501 (by decide)
  have h7 : Entails.eval a c2670 := h 2669 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7572 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c866, some c1285, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7572 : lratChecker f7572 p7572 = .success := by decide +kernel
theorem unsat7572 : Unsatisfiable (PosFin 65) f7572 := by
  apply lratCheckerSound f7572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7572
  · intro a ha; simp [p7572] at ha; subst a; trivial
  · exact checked7572
theorem derived7572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7572 := by
  apply localUnsat_implies_entails f7572 [c866, c1285] c7572 unsat7572 (by rfl) a
  have h0 : Entails.eval a c866 := h 865 (by decide)
  have h1 : Entails.eval a c1285 := h 1284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7573 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1416, some c2061, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7573 : lratChecker f7573 p7573 = .success := by decide +kernel
theorem unsat7573 : Unsatisfiable (PosFin 65) f7573 := by
  apply lratCheckerSound f7573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7573
  · intro a ha; simp [p7573] at ha; subst a; trivial
  · exact checked7573
theorem derived7573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7573 := by
  apply localUnsat_implies_entails f7573 [c1416, c2061] c7573 unsat7573 (by rfl) a
  have h0 : Entails.eval a c1416 := h 1415 (by decide)
  have h1 : Entails.eval a c2061 := h 2060 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7574 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1083, some c1090, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7574 : lratChecker f7574 p7574 = .success := by decide +kernel
theorem unsat7574 : Unsatisfiable (PosFin 65) f7574 := by
  apply lratCheckerSound f7574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7574
  · intro a ha; simp [p7574] at ha; subst a; trivial
  · exact checked7574
theorem derived7574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7574 := by
  apply localUnsat_implies_entails f7574 [c1083, c1090] c7574 unsat7574 (by rfl) a
  have h0 : Entails.eval a c1083 := h 1082 (by decide)
  have h1 : Entails.eval a c1090 := h 1089 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7575 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7572, some c7573, some c2025, some c7574, some c2109, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7575 : lratChecker f7575 p7575 = .success := by decide +kernel
theorem unsat7575 : Unsatisfiable (PosFin 65) f7575 := by
  apply lratCheckerSound f7575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7575
  · intro a ha; simp [p7575] at ha; subst a; trivial
  · exact checked7575
theorem derived7575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7575 := by
  apply localUnsat_implies_entails f7575 [c7572, c7573, c2025, c7574, c2109] c7575 unsat7575 (by rfl) a
  have h0 : Entails.eval a c7572 := derived7572 a h
  have h1 : Entails.eval a c7573 := derived7573 a h
  have h2 : Entails.eval a c2025 := h 2024 (by decide)
  have h3 : Entails.eval a c7574 := derived7574 a h
  have h4 : Entails.eval a c2109 := h 2108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7576 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1416, some c1146, some c2584, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7576 : lratChecker f7576 p7576 = .success := by decide +kernel
theorem unsat7576 : Unsatisfiable (PosFin 65) f7576 := by
  apply lratCheckerSound f7576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7576
  · intro a ha; simp [p7576] at ha; subst a; trivial
  · exact checked7576
theorem derived7576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7576 := by
  apply localUnsat_implies_entails f7576 [c1416, c1146, c2584] c7576 unsat7576 (by rfl) a
  have h0 : Entails.eval a c1416 := h 1415 (by decide)
  have h1 : Entails.eval a c1146 := h 1145 (by decide)
  have h2 : Entails.eval a c2584 := h 2583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7577 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c136, some c2046, some c1937, some c3077, some c3076, some c2354, some c1339, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7577 : lratChecker f7577 p7577 = .success := by decide +kernel
theorem unsat7577 : Unsatisfiable (PosFin 65) f7577 := by
  apply lratCheckerSound f7577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7577
  · intro a ha; simp [p7577] at ha; subst a; trivial
  · exact checked7577
theorem derived7577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7577 := by
  apply localUnsat_implies_entails f7577 [c136, c2046, c1937, c3077, c3076, c2354, c1339] c7577 unsat7577 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c2046 := h 2045 (by decide)
  have h2 : Entails.eval a c1937 := h 1936 (by decide)
  have h3 : Entails.eval a c3077 := h 3076 (by decide)
  have h4 : Entails.eval a c3076 := h 3075 (by decide)
  have h5 : Entails.eval a c2354 := h 2353 (by decide)
  have h6 : Entails.eval a c1339 := h 1338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7578 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7572, some c7575, some c7576, some c7577, some c7574, some c2153, some c2353, some c2322, some c1148, some c1158, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7578 : lratChecker f7578 p7578 = .success := by decide +kernel
theorem unsat7578 : Unsatisfiable (PosFin 65) f7578 := by
  apply lratCheckerSound f7578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7578
  · intro a ha; simp [p7578] at ha; subst a; trivial
  · exact checked7578
theorem derived7578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7578 := by
  apply localUnsat_implies_entails f7578 [c7572, c7575, c7576, c7577, c7574, c2153, c2353, c2322, c1148, c1158] c7578 unsat7578 (by rfl) a
  have h0 : Entails.eval a c7572 := derived7572 a h
  have h1 : Entails.eval a c7575 := derived7575 a h
  have h2 : Entails.eval a c7576 := derived7576 a h
  have h3 : Entails.eval a c7577 := derived7577 a h
  have h4 : Entails.eval a c7574 := derived7574 a h
  have h5 : Entails.eval a c2153 := h 2152 (by decide)
  have h6 : Entails.eval a c2353 := h 2352 (by decide)
  have h7 : Entails.eval a c2322 := h 2321 (by decide)
  have h8 : Entails.eval a c1148 := h 1147 (by decide)
  have h9 : Entails.eval a c1158 := h 1157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7579 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7578, some c1341, some c2183, some c903, some c902, some c931, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7579 : lratChecker f7579 p7579 = .success := by decide +kernel
theorem unsat7579 : Unsatisfiable (PosFin 65) f7579 := by
  apply lratCheckerSound f7579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7579
  · intro a ha; simp [p7579] at ha; subst a; trivial
  · exact checked7579
theorem derived7579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7579 := by
  apply localUnsat_implies_entails f7579 [c7578, c1341, c2183, c903, c902, c931] c7579 unsat7579 (by rfl) a
  have h0 : Entails.eval a c7578 := derived7578 a h
  have h1 : Entails.eval a c1341 := h 1340 (by decide)
  have h2 : Entails.eval a c2183 := h 2182 (by decide)
  have h3 : Entails.eval a c903 := h 902 (by decide)
  have h4 : Entails.eval a c902 := h 901 (by decide)
  have h5 : Entails.eval a c931 := h 930 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7580 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7550, some c7571, some c7569, some c7559, some c7579, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7580 : lratChecker f7580 p7580 = .success := by decide +kernel
theorem unsat7580 : Unsatisfiable (PosFin 65) f7580 := by
  apply lratCheckerSound f7580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7580
  · intro a ha; simp [p7580] at ha; subst a; trivial
  · exact checked7580
theorem derived7580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7580 := by
  apply localUnsat_implies_entails f7580 [c7470, c7550, c7571, c7569, c7559, c7579] c7580 unsat7580 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7550 := derived7550 a h
  have h2 : Entails.eval a c7571 := derived7571 a h
  have h3 : Entails.eval a c7569 := derived7569 a h
  have h4 : Entails.eval a c7559 := derived7559 a h
  have h5 : Entails.eval a c7579 := derived7579 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7580

end CochromaticTwenty.Certificates.FixedCore1
