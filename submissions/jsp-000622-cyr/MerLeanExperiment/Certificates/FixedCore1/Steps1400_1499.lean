import MerLeanExperiment.Certificates.FixedCore1.Steps1300_1399

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7281 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7281 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c279, some c253, some c267, some c261, some c7135, some c247, some c7201, some c7275, some c1960, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7281 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7281 : lratChecker f7281 p7281 = .success := by decide +kernel
theorem unsat7281 : Unsatisfiable (PosFin 65) f7281 := by
  apply lratCheckerSound f7281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7281
  · intro a ha; simp [p7281] at ha; subst a; trivial
  · exact checked7281
theorem derived7281 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7281 := by
  apply localUnsat_implies_entails f7281 [c279, c253, c267, c261, c7135, c247, c7201, c7275, c1960] c7281 unsat7281 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c7135 := derived7135 a h
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c7201 := derived7201 a h
  have h7 : Entails.eval a c7275 := derived7275 a h
  have h8 : Entails.eval a c1960 := h 1959 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7282 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7282 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7272, some c1783, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7282 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7282 : lratChecker f7282 p7282 = .success := by decide +kernel
theorem unsat7282 : Unsatisfiable (PosFin 65) f7282 := by
  apply lratCheckerSound f7282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7282
  · intro a ha; simp [p7282] at ha; subst a; trivial
  · exact checked7282
theorem derived7282 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7282 := by
  apply localUnsat_implies_entails f7282 [c7272, c1783] c7282 unsat7282 (by rfl) a
  have h0 : Entails.eval a c7272 := derived7272 a h
  have h1 : Entails.eval a c1783 := h 1782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7283 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7283 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7281, some c7282, some c1732, some c1782, some c2018, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7283 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7283 : lratChecker f7283 p7283 = .success := by decide +kernel
theorem unsat7283 : Unsatisfiable (PosFin 65) f7283 := by
  apply lratCheckerSound f7283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7283
  · intro a ha; simp [p7283] at ha; subst a; trivial
  · exact checked7283
theorem derived7283 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7283 := by
  apply localUnsat_implies_entails f7283 [c7281, c7282, c1732, c1782, c2018] c7283 unsat7283 (by rfl) a
  have h0 : Entails.eval a c7281 := derived7281 a h
  have h1 : Entails.eval a c7282 := derived7282 a h
  have h2 : Entails.eval a c1732 := h 1731 (by decide)
  have h3 : Entails.eval a c1782 := h 1781 (by decide)
  have h4 : Entails.eval a c2018 := h 2017 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7284 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7284 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7268, some c7274, some c7278, some c7280, some c7283, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7284 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7284 : lratChecker f7284 p7284 = .success := by decide +kernel
theorem unsat7284 : Unsatisfiable (PosFin 65) f7284 := by
  apply lratCheckerSound f7284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7284
  · intro a ha; simp [p7284] at ha; subst a; trivial
  · exact checked7284
theorem derived7284 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7284 := by
  apply localUnsat_implies_entails f7284 [c7268, c7274, c7278, c7280, c7283] c7284 unsat7284 (by rfl) a
  have h0 : Entails.eval a c7268 := derived7268 a h
  have h1 : Entails.eval a c7274 := derived7274 a h
  have h2 : Entails.eval a c7278 := derived7278 a h
  have h3 : Entails.eval a c7280 := derived7280 a h
  have h4 : Entails.eval a c7283 := derived7283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7285 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7285 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c282, some c270, some c253, some c285, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7285 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7285 : lratChecker f7285 p7285 = .success := by decide +kernel
theorem unsat7285 : Unsatisfiable (PosFin 65) f7285 := by
  apply lratCheckerSound f7285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7285
  · intro a ha; simp [p7285] at ha; subst a; trivial
  · exact checked7285
theorem derived7285 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7285 := by
  apply localUnsat_implies_entails f7285 [c282, c270, c253, c285] c7285 unsat7285 (by rfl) a
  have h0 : Entails.eval a c282 := h 281 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7286 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7286 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c414, some c1811, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7286 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7286 : lratChecker f7286 p7286 = .success := by decide +kernel
theorem unsat7286 : Unsatisfiable (PosFin 65) f7286 := by
  apply lratCheckerSound f7286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7286
  · intro a ha; simp [p7286] at ha; subst a; trivial
  · exact checked7286
theorem derived7286 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7286 := by
  apply localUnsat_implies_entails f7286 [c414, c1811] c7286 unsat7286 (by rfl) a
  have h0 : Entails.eval a c414 := h 413 (by decide)
  have h1 : Entails.eval a c1811 := h 1810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7287 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨24, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7287 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1767, some c221, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7287 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7287 : lratChecker f7287 p7287 = .success := by decide +kernel
theorem unsat7287 : Unsatisfiable (PosFin 65) f7287 := by
  apply lratCheckerSound f7287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7287
  · intro a ha; simp [p7287] at ha; subst a; trivial
  · exact checked7287
theorem derived7287 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7287 := by
  apply localUnsat_implies_entails f7287 [c1767, c221] c7287 unsat7287 (by rfl) a
  have h0 : Entails.eval a c1767 := h 1766 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7288 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7288 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c416, some c405, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7288 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7288 : lratChecker f7288 p7288 = .success := by decide +kernel
theorem unsat7288 : Unsatisfiable (PosFin 65) f7288 := by
  apply lratCheckerSound f7288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7288
  · intro a ha; simp [p7288] at ha; subst a; trivial
  · exact checked7288
theorem derived7288 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7288 := by
  apply localUnsat_implies_entails f7288 [c416, c405] c7288 unsat7288 (by rfl) a
  have h0 : Entails.eval a c416 := h 415 (by decide)
  have h1 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7289 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7289 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7262, some c7286, some c7288, some c1814, some c1806, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7289 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7289 : lratChecker f7289 p7289 = .success := by decide +kernel
theorem unsat7289 : Unsatisfiable (PosFin 65) f7289 := by
  apply lratCheckerSound f7289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7289
  · intro a ha; simp [p7289] at ha; subst a; trivial
  · exact checked7289
theorem derived7289 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7289 := by
  apply localUnsat_implies_entails f7289 [c7262, c7286, c7288, c1814, c1806] c7289 unsat7289 (by rfl) a
  have h0 : Entails.eval a c7262 := derived7262 a h
  have h1 : Entails.eval a c7286 := derived7286 a h
  have h2 : Entails.eval a c7288 := derived7288 a h
  have h3 : Entails.eval a c1814 := h 1813 (by decide)
  have h4 : Entails.eval a c1806 := h 1805 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7290 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7290 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7239, some c337, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7290 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7290 : lratChecker f7290 p7290 = .success := by decide +kernel
theorem unsat7290 : Unsatisfiable (PosFin 65) f7290 := by
  apply lratCheckerSound f7290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7290
  · intro a ha; simp [p7290] at ha; subst a; trivial
  · exact checked7290
theorem derived7290 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7290 := by
  apply localUnsat_implies_entails f7290 [c7239, c337] c7290 unsat7290 (by rfl) a
  have h0 : Entails.eval a c7239 := derived7239 a h
  have h1 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7291 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7291 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c220, some c252, some c1766, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7291 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7291 : lratChecker f7291 p7291 = .success := by decide +kernel
theorem unsat7291 : Unsatisfiable (PosFin 65) f7291 := by
  apply lratCheckerSound f7291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7291
  · intro a ha; simp [p7291] at ha; subst a; trivial
  · exact checked7291
theorem derived7291 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7291 := by
  apply localUnsat_implies_entails f7291 [c220, c252, c1766] c7291 unsat7291 (by rfl) a
  have h0 : Entails.eval a c220 := h 219 (by decide)
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c1766 := h 1765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7292 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7292 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7284, some c7291, some c335, some c383, some c1791, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7292 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7292 : lratChecker f7292 p7292 = .success := by decide +kernel
theorem unsat7292 : Unsatisfiable (PosFin 65) f7292 := by
  apply lratCheckerSound f7292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7292
  · intro a ha; simp [p7292] at ha; subst a; trivial
  · exact checked7292
theorem derived7292 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7292 := by
  apply localUnsat_implies_entails f7292 [c7284, c7291, c335, c383, c1791] c7292 unsat7292 (by rfl) a
  have h0 : Entails.eval a c7284 := derived7284 a h
  have h1 : Entails.eval a c7291 := derived7291 a h
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c1791 := h 1790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7293 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7293 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7289, some c7290, some c7292, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7293 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7293 : lratChecker f7293 p7293 = .success := by decide +kernel
theorem unsat7293 : Unsatisfiable (PosFin 65) f7293 := by
  apply lratCheckerSound f7293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7293
  · intro a ha; simp [p7293] at ha; subst a; trivial
  · exact checked7293
theorem derived7293 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7293 := by
  apply localUnsat_implies_entails f7293 [c7289, c7290, c7292] c7293 unsat7293 (by rfl) a
  have h0 : Entails.eval a c7289 := derived7289 a h
  have h1 : Entails.eval a c7290 := derived7290 a h
  have h2 : Entails.eval a c7292 := derived7292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7294 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7294 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c336, some c340, some c357, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7294 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7294 : lratChecker f7294 p7294 = .success := by decide +kernel
theorem unsat7294 : Unsatisfiable (PosFin 65) f7294 := by
  apply lratCheckerSound f7294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7294
  · intro a ha; simp [p7294] at ha; subst a; trivial
  · exact checked7294
theorem derived7294 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7294 := by
  apply localUnsat_implies_entails f7294 [c336, c340, c357] c7294 unsat7294 (by rfl) a
  have h0 : Entails.eval a c336 := h 335 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7295 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7295 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c386, some c1792, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7295 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7295 : lratChecker f7295 p7295 = .success := by decide +kernel
theorem unsat7295 : Unsatisfiable (PosFin 65) f7295 := by
  apply lratCheckerSound f7295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7295
  · intro a ha; simp [p7295] at ha; subst a; trivial
  · exact checked7295
theorem derived7295 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7295 := by
  apply localUnsat_implies_entails f7295 [c386, c1792] c7295 unsat7295 (by rfl) a
  have h0 : Entails.eval a c386 := h 385 (by decide)
  have h1 : Entails.eval a c1792 := h 1791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7296 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7296 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c279, some c253, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7296 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7296 : lratChecker f7296 p7296 = .success := by decide +kernel
theorem unsat7296 : Unsatisfiable (PosFin 65) f7296 := by
  apply lratCheckerSound f7296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7296
  · intro a ha; simp [p7296] at ha; subst a; trivial
  · exact checked7296
theorem derived7296 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7296 := by
  apply localUnsat_implies_entails f7296 [c279, c253] c7296 unsat7296 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7297 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7297 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7296, some c7287, some c241, some c1778, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7297 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7297 : lratChecker f7297 p7297 = .success := by decide +kernel
theorem unsat7297 : Unsatisfiable (PosFin 65) f7297 := by
  apply lratCheckerSound f7297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7297
  · intro a ha; simp [p7297] at ha; subst a; trivial
  · exact checked7297
theorem derived7297 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7297 := by
  apply localUnsat_implies_entails f7297 [c7296, c7287, c241, c1778] c7297 unsat7297 (by rfl) a
  have h0 : Entails.eval a c7296 := derived7296 a h
  have h1 : Entails.eval a c7287 := derived7287 a h
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c1778 := h 1777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7298 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7298 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c270, some c253, some c285, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7298 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7298 : lratChecker f7298 p7298 = .success := by decide +kernel
theorem unsat7298 : Unsatisfiable (PosFin 65) f7298 := by
  apply lratCheckerSound f7298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7298
  · intro a ha; simp [p7298] at ha; subst a; trivial
  · exact checked7298
theorem derived7298 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7298 := by
  apply localUnsat_implies_entails f7298 [c270, c253, c285] c7298 unsat7298 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7299 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7299 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1714, some c1710, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7299 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7299 : lratChecker f7299 p7299 = .success := by decide +kernel
theorem unsat7299 : Unsatisfiable (PosFin 65) f7299 := by
  apply lratCheckerSound f7299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7299
  · intro a ha; simp [p7299] at ha; subst a; trivial
  · exact checked7299
theorem derived7299 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7299 := by
  apply localUnsat_implies_entails f7299 [c1714, c1710] c7299 unsat7299 (by rfl) a
  have h0 : Entails.eval a c1714 := h 1713 (by decide)
  have h1 : Entails.eval a c1710 := h 1709 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7300 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7300 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1590, some c1586, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7300 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7300 : lratChecker f7300 p7300 = .success := by decide +kernel
theorem unsat7300 : Unsatisfiable (PosFin 65) f7300 := by
  apply lratCheckerSound f7300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7300
  · intro a ha; simp [p7300] at ha; subst a; trivial
  · exact checked7300
theorem derived7300 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7300 := by
  apply localUnsat_implies_entails f7300 [c1590, c1586] c7300 unsat7300 (by rfl) a
  have h0 : Entails.eval a c1590 := h 1589 (by decide)
  have h1 : Entails.eval a c1586 := h 1585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7301 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7301 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c389, some c406, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7301 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7301 : lratChecker f7301 p7301 = .success := by decide +kernel
theorem unsat7301 : Unsatisfiable (PosFin 65) f7301 := by
  apply lratCheckerSound f7301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7301
  · intro a ha; simp [p7301] at ha; subst a; trivial
  · exact checked7301
theorem derived7301 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7301 := by
  apply localUnsat_implies_entails f7301 [c389, c406] c7301 unsat7301 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c406 := h 405 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7302 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7302 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7293, some c7294, some c7295, some c7301, some c1795, some c1807, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7302 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7302 : lratChecker f7302 p7302 = .success := by decide +kernel
theorem unsat7302 : Unsatisfiable (PosFin 65) f7302 := by
  apply lratCheckerSound f7302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7302
  · intro a ha; simp [p7302] at ha; subst a; trivial
  · exact checked7302
theorem derived7302 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7302 := by
  apply localUnsat_implies_entails f7302 [c7293, c7294, c7295, c7301, c1795, c1807] c7302 unsat7302 (by rfl) a
  have h0 : Entails.eval a c7293 := derived7293 a h
  have h1 : Entails.eval a c7294 := derived7294 a h
  have h2 : Entails.eval a c7295 := derived7295 a h
  have h3 : Entails.eval a c7301 := derived7301 a h
  have h4 : Entails.eval a c1795 := h 1794 (by decide)
  have h5 : Entails.eval a c1807 := h 1806 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7303 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7303 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c361, some c7244, some c256, some c7259, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7303 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7303 : lratChecker f7303 p7303 = .success := by decide +kernel
theorem unsat7303 : Unsatisfiable (PosFin 65) f7303 := by
  apply lratCheckerSound f7303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7303
  · intro a ha; simp [p7303] at ha; subst a; trivial
  · exact checked7303
theorem derived7303 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7303 := by
  apply localUnsat_implies_entails f7303 [c361, c7244, c256, c7259] c7303 unsat7303 (by rfl) a
  have h0 : Entails.eval a c361 := h 360 (by decide)
  have h1 : Entails.eval a c7244 := derived7244 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c7259 := derived7259 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7304 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7304 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c350, some c335, some c355, some c362, some c356, some c357, some c353, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7304 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7304 : lratChecker f7304 p7304 = .success := by decide +kernel
theorem unsat7304 : Unsatisfiable (PosFin 65) f7304 := by
  apply lratCheckerSound f7304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7304
  · intro a ha; simp [p7304] at ha; subst a; trivial
  · exact checked7304
theorem derived7304 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7304 := by
  apply localUnsat_implies_entails f7304 [c350, c335, c355, c362, c356, c357, c353] c7304 unsat7304 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7305 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7305 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7291, some c7303, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7305 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7305 : lratChecker f7305 p7305 = .success := by decide +kernel
theorem unsat7305 : Unsatisfiable (PosFin 65) f7305 := by
  apply lratCheckerSound f7305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7305
  · intro a ha; simp [p7305] at ha; subst a; trivial
  · exact checked7305
theorem derived7305 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7305 := by
  apply localUnsat_implies_entails f7305 [c7291, c7303] c7305 unsat7305 (by rfl) a
  have h0 : Entails.eval a c7291 := derived7291 a h
  have h1 : Entails.eval a c7303 := derived7303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7306 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7306 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7302, some c7304, some c7305, some c330, some c339, some c354, some c341, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7306 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7306 : lratChecker f7306 p7306 = .success := by decide +kernel
theorem unsat7306 : Unsatisfiable (PosFin 65) f7306 := by
  apply lratCheckerSound f7306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7306
  · intro a ha; simp [p7306] at ha; subst a; trivial
  · exact checked7306
theorem derived7306 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7306 := by
  apply localUnsat_implies_entails f7306 [c7302, c7304, c7305, c330, c339, c354, c341] c7306 unsat7306 (by rfl) a
  have h0 : Entails.eval a c7302 := derived7302 a h
  have h1 : Entails.eval a c7304 := derived7304 a h
  have h2 : Entails.eval a c7305 := derived7305 a h
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7307 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7307 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c256, some c279, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7307 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7307 : lratChecker f7307 p7307 = .success := by decide +kernel
theorem unsat7307 : Unsatisfiable (PosFin 65) f7307 := by
  apply lratCheckerSound f7307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7307
  · intro a ha; simp [p7307] at ha; subst a; trivial
  · exact checked7307
theorem derived7307 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7307 := by
  apply localUnsat_implies_entails f7307 [c256, c279] c7307 unsat7307 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7308 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7308 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1593, some c7244, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7308 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7308 : lratChecker f7308 p7308 = .success := by decide +kernel
theorem unsat7308 : Unsatisfiable (PosFin 65) f7308 := by
  apply lratCheckerSound f7308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7308
  · intro a ha; simp [p7308] at ha; subst a; trivial
  · exact checked7308
theorem derived7308 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7308 := by
  apply localUnsat_implies_entails f7308 [c1593, c7244] c7308 unsat7308 (by rfl) a
  have h0 : Entails.eval a c1593 := h 1592 (by decide)
  have h1 : Entails.eval a c7244 := derived7244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7309 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7309 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7307, some c241, some c1778, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7309 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7309 : lratChecker f7309 p7309 = .success := by decide +kernel
theorem unsat7309 : Unsatisfiable (PosFin 65) f7309 := by
  apply lratCheckerSound f7309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7309
  · intro a ha; simp [p7309] at ha; subst a; trivial
  · exact checked7309
theorem derived7309 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7309 := by
  apply localUnsat_implies_entails f7309 [c7307, c241, c1778] c7309 unsat7309 (by rfl) a
  have h0 : Entails.eval a c7307 := derived7307 a h
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c1778 := h 1777 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7310 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7310 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c255, some c248, some c265, some c258, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7310 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7310 : lratChecker f7310 p7310 = .success := by decide +kernel
theorem unsat7310 : Unsatisfiable (PosFin 65) f7310 := by
  apply lratCheckerSound f7310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7310
  · intro a ha; simp [p7310] at ha; subst a; trivial
  · exact checked7310
theorem derived7310 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7310 := by
  apply localUnsat_implies_entails f7310 [c255, c248, c265, c258] c7310 unsat7310 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7311 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7311 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c383, some c1791, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7311 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7311 : lratChecker f7311 p7311 = .success := by decide +kernel
theorem unsat7311 : Unsatisfiable (PosFin 65) f7311 := by
  apply lratCheckerSound f7311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7311
  · intro a ha; simp [p7311] at ha; subst a; trivial
  · exact checked7311
theorem derived7311 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7311 := by
  apply localUnsat_implies_entails f7311 [c383, c1791] c7311 unsat7311 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c1791 := h 1790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7312 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7312 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1622, some c1627, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7312 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7312 : lratChecker f7312 p7312 = .success := by decide +kernel
theorem unsat7312 : Unsatisfiable (PosFin 65) f7312 := by
  apply lratCheckerSound f7312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7312
  · intro a ha; simp [p7312] at ha; subst a; trivial
  · exact checked7312
theorem derived7312 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7312 := by
  apply localUnsat_implies_entails f7312 [c1622, c1627] c7312 unsat7312 (by rfl) a
  have h0 : Entails.eval a c1622 := h 1621 (by decide)
  have h1 : Entails.eval a c1627 := h 1626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7313 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7313 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c384, some c413, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7313 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7313 : lratChecker f7313 p7313 = .success := by decide +kernel
theorem unsat7313 : Unsatisfiable (PosFin 65) f7313 := by
  apply lratCheckerSound f7313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7313
  · intro a ha; simp [p7313] at ha; subst a; trivial
  · exact checked7313
theorem derived7313 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7313 := by
  apply localUnsat_implies_entails f7313 [c384, c413] c7313 unsat7313 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c413 := h 412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7314 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7314 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7311, some c7313, some c1805, some c1810, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7314 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7314 : lratChecker f7314 p7314 = .success := by decide +kernel
theorem unsat7314 : Unsatisfiable (PosFin 65) f7314 := by
  apply lratCheckerSound f7314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7314
  · intro a ha; simp [p7314] at ha; subst a; trivial
  · exact checked7314
theorem derived7314 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7314 := by
  apply localUnsat_implies_entails f7314 [c7311, c7313, c1805, c1810] c7314 unsat7314 (by rfl) a
  have h0 : Entails.eval a c7311 := derived7311 a h
  have h1 : Entails.eval a c7313 := derived7313 a h
  have h2 : Entails.eval a c1805 := h 1804 (by decide)
  have h3 : Entails.eval a c1810 := h 1809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7315 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7315 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c384, some c399, some c404, some c401, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7315 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7315 : lratChecker f7315 p7315 = .success := by decide +kernel
theorem unsat7315 : Unsatisfiable (PosFin 65) f7315 := by
  apply lratCheckerSound f7315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7315
  · intro a ha; simp [p7315] at ha; subst a; trivial
  · exact checked7315
theorem derived7315 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7315 := by
  apply localUnsat_implies_entails f7315 [c384, c399, c404, c401] c7315 unsat7315 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c399 := h 398 (by decide)
  have h2 : Entails.eval a c404 := h 403 (by decide)
  have h3 : Entails.eval a c401 := h 400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7316 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7316 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1806, some c1799, some c1807, some c1803, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p7316 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7316 : lratChecker f7316 p7316 = .success := by decide +kernel
theorem unsat7316 : Unsatisfiable (PosFin 65) f7316 := by
  apply lratCheckerSound f7316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7316
  · intro a ha; simp [p7316] at ha; subst a; trivial
  · exact checked7316
theorem derived7316 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7316 := by
  apply localUnsat_implies_entails f7316 [c1806, c1799, c1807, c1803] c7316 unsat7316 (by rfl) a
  have h0 : Entails.eval a c1806 := h 1805 (by decide)
  have h1 : Entails.eval a c1799 := h 1798 (by decide)
  have h2 : Entails.eval a c1807 := h 1806 (by decide)
  have h3 : Entails.eval a c1803 := h 1802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7317 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7317 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7314, some c7315, some c7316, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7317 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7317 : lratChecker f7317 p7317 = .success := by decide +kernel
theorem unsat7317 : Unsatisfiable (PosFin 65) f7317 := by
  apply lratCheckerSound f7317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7317
  · intro a ha; simp [p7317] at ha; subst a; trivial
  · exact checked7317
theorem derived7317 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7317 := by
  apply localUnsat_implies_entails f7317 [c7314, c7315, c7316] c7317 unsat7317 (by rfl) a
  have h0 : Entails.eval a c7314 := derived7314 a h
  have h1 : Entails.eval a c7315 := derived7315 a h
  have h2 : Entails.eval a c7316 := derived7316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7318 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7318 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7291, some c7309, some c7308, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7318 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7318 : lratChecker f7318 p7318 = .success := by decide +kernel
theorem unsat7318 : Unsatisfiable (PosFin 65) f7318 := by
  apply lratCheckerSound f7318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7318
  · intro a ha; simp [p7318] at ha; subst a; trivial
  · exact checked7318
theorem derived7318 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7318 := by
  apply localUnsat_implies_entails f7318 [c7291, c7309, c7308] c7318 unsat7318 (by rfl) a
  have h0 : Entails.eval a c7291 := derived7291 a h
  have h1 : Entails.eval a c7309 := derived7309 a h
  have h2 : Entails.eval a c7308 := derived7308 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7319 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7319 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c379, some c393, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7319 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7319 : lratChecker f7319 p7319 = .success := by decide +kernel
theorem unsat7319 : Unsatisfiable (PosFin 65) f7319 := by
  apply lratCheckerSound f7319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7319
  · intro a ha; simp [p7319] at ha; subst a; trivial
  · exact checked7319
theorem derived7319 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7319 := by
  apply localUnsat_implies_entails f7319 [c379, c393] c7319 unsat7319 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7320 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7320 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7290, some c7317, some c7319, some c1794, some c1804, some c1810, some c1803, some c1809, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7320 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7320 : lratChecker f7320 p7320 = .success := by decide +kernel
theorem unsat7320 : Unsatisfiable (PosFin 65) f7320 := by
  apply lratCheckerSound f7320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7320
  · intro a ha; simp [p7320] at ha; subst a; trivial
  · exact checked7320
theorem derived7320 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7320 := by
  apply localUnsat_implies_entails f7320 [c7290, c7317, c7319, c1794, c1804, c1810, c1803, c1809] c7320 unsat7320 (by rfl) a
  have h0 : Entails.eval a c7290 := derived7290 a h
  have h1 : Entails.eval a c7317 := derived7317 a h
  have h2 : Entails.eval a c7319 := derived7319 a h
  have h3 : Entails.eval a c1794 := h 1793 (by decide)
  have h4 : Entails.eval a c1804 := h 1803 (by decide)
  have h5 : Entails.eval a c1810 := h 1809 (by decide)
  have h6 : Entails.eval a c1803 := h 1802 (by decide)
  have h7 : Entails.eval a c1809 := h 1808 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7321 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7321 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7320, some c7316, some c379, some c388, some c403, some c391, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7321 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7321 : lratChecker f7321 p7321 = .success := by decide +kernel
theorem unsat7321 : Unsatisfiable (PosFin 65) f7321 := by
  apply lratCheckerSound f7321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7321
  · intro a ha; simp [p7321] at ha; subst a; trivial
  · exact checked7321
theorem derived7321 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7321 := by
  apply localUnsat_implies_entails f7321 [c7320, c7316, c379, c388, c403, c391] c7321 unsat7321 (by rfl) a
  have h0 : Entails.eval a c7320 := derived7320 a h
  have h1 : Entails.eval a c7316 := derived7316 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c403 := h 402 (by decide)
  have h5 : Entails.eval a c391 := h 390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7322 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7322 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7302, some c7306, some c7317, some c7318, some c7321, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7322 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7322 : lratChecker f7322 p7322 = .success := by decide +kernel
theorem unsat7322 : Unsatisfiable (PosFin 65) f7322 := by
  apply lratCheckerSound f7322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7322
  · intro a ha; simp [p7322] at ha; subst a; trivial
  · exact checked7322
theorem derived7322 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7322 := by
  apply localUnsat_implies_entails f7322 [c7302, c7306, c7317, c7318, c7321] c7322 unsat7322 (by rfl) a
  have h0 : Entails.eval a c7302 := derived7302 a h
  have h1 : Entails.eval a c7306 := derived7306 a h
  have h2 : Entails.eval a c7317 := derived7317 a h
  have h3 : Entails.eval a c7318 := derived7318 a h
  have h4 : Entails.eval a c7321 := derived7321 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7323 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7323 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7244, some c1621, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7323 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7323 : lratChecker f7323 p7323 = .success := by decide +kernel
theorem unsat7323 : Unsatisfiable (PosFin 65) f7323 := by
  apply lratCheckerSound f7323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7323
  · intro a ha; simp [p7323] at ha; subst a; trivial
  · exact checked7323
theorem derived7323 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7323 := by
  apply localUnsat_implies_entails f7323 [c7244, c1621] c7323 unsat7323 (by rfl) a
  have h0 : Entails.eval a c7244 := derived7244 a h
  have h1 : Entails.eval a c1621 := h 1620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7324 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7324 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c385, some c411, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7324 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7324 : lratChecker f7324 p7324 = .success := by decide +kernel
theorem unsat7324 : Unsatisfiable (PosFin 65) f7324 := by
  apply lratCheckerSound f7324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7324
  · intro a ha; simp [p7324] at ha; subst a; trivial
  · exact checked7324
theorem derived7324 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7324 := by
  apply localUnsat_implies_entails f7324 [c385, c411] c7324 unsat7324 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c411 := h 410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7325 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7325 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1775, some c238, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7325 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7325 : lratChecker f7325 p7325 = .success := by decide +kernel
theorem unsat7325 : Unsatisfiable (PosFin 65) f7325 := by
  apply lratCheckerSound f7325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7325
  · intro a ha; simp [p7325] at ha; subst a; trivial
  · exact checked7325
theorem derived7325 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7325 := by
  apply localUnsat_implies_entails f7325 [c1775, c238] c7325 unsat7325 (by rfl) a
  have h0 : Entails.eval a c1775 := h 1774 (by decide)
  have h1 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7326 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7326 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7310, some c7323, some c7312, some c7325, some c243, some c1723, some c1647, some c1919, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7326 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7326 : lratChecker f7326 p7326 = .success := by decide +kernel
theorem unsat7326 : Unsatisfiable (PosFin 65) f7326 := by
  apply lratCheckerSound f7326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7326
  · intro a ha; simp [p7326] at ha; subst a; trivial
  · exact checked7326
theorem derived7326 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7326 := by
  apply localUnsat_implies_entails f7326 [c7310, c7323, c7312, c7325, c243, c1723, c1647, c1919] c7326 unsat7326 (by rfl) a
  have h0 : Entails.eval a c7310 := derived7310 a h
  have h1 : Entails.eval a c7323 := derived7323 a h
  have h2 : Entails.eval a c7312 := derived7312 a h
  have h3 : Entails.eval a c7325 := derived7325 a h
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c1723 := h 1722 (by decide)
  have h6 : Entails.eval a c1647 := h 1646 (by decide)
  have h7 : Entails.eval a c1919 := h 1918 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7327 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7327 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7322, some c7302, some c7305, some c350, some c355, some c332, some c357, some c362, some c7324, some c7326, some c1658, some c1688, some c2197, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7327 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7327 : lratChecker f7327 p7327 = .success := by decide +kernel
theorem unsat7327 : Unsatisfiable (PosFin 65) f7327 := by
  apply lratCheckerSound f7327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7327
  · intro a ha; simp [p7327] at ha; subst a; trivial
  · exact checked7327
theorem derived7327 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7327 := by
  apply localUnsat_implies_entails f7327 [c7322, c7302, c7305, c350, c355, c332, c357, c362, c7324, c7326, c1658, c1688, c2197] c7327 unsat7327 (by rfl) a
  have h0 : Entails.eval a c7322 := derived7322 a h
  have h1 : Entails.eval a c7302 := derived7302 a h
  have h2 : Entails.eval a c7305 := derived7305 a h
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c332 := h 331 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c7324 := derived7324 a h
  have h9 : Entails.eval a c7326 := derived7326 a h
  have h10 : Entails.eval a c1658 := h 1657 (by decide)
  have h11 : Entails.eval a c1688 := h 1687 (by decide)
  have h12 : Entails.eval a c2197 := h 2196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7328 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7328 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7322, some c7302, some c7327, some c347, some c354, some c341, some c332, some c365, some c360, some c367, some c362, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7328 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7328 : lratChecker f7328 p7328 = .success := by decide +kernel
theorem unsat7328 : Unsatisfiable (PosFin 65) f7328 := by
  apply lratCheckerSound f7328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7328
  · intro a ha; simp [p7328] at ha; subst a; trivial
  · exact checked7328
theorem derived7328 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7328 := by
  apply localUnsat_implies_entails f7328 [c7322, c7302, c7327, c347, c354, c341, c332, c365, c360, c367, c362] c7328 unsat7328 (by rfl) a
  have h0 : Entails.eval a c7322 := derived7322 a h
  have h1 : Entails.eval a c7302 := derived7302 a h
  have h2 : Entails.eval a c7327 := derived7327 a h
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c360 := h 359 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7329 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7329 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c385, some c404, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7329 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7329 : lratChecker f7329 p7329 = .success := by decide +kernel
theorem unsat7329 : Unsatisfiable (PosFin 65) f7329 := by
  apply lratCheckerSound f7329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7329
  · intro a ha; simp [p7329] at ha; subst a; trivial
  · exact checked7329
theorem derived7329 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7329 := by
  apply localUnsat_implies_entails f7329 [c385, c404] c7329 unsat7329 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c404 := h 403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7330 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7330 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7302, some c7328, some c7318, some c7322, some c7329, some c1798, some c1789, some c1805, some c7326, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7330 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7330 : lratChecker f7330 p7330 = .success := by decide +kernel
theorem unsat7330 : Unsatisfiable (PosFin 65) f7330 := by
  apply lratCheckerSound f7330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7330
  · intro a ha; simp [p7330] at ha; subst a; trivial
  · exact checked7330
theorem derived7330 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7330 := by
  apply localUnsat_implies_entails f7330 [c7302, c7328, c7318, c7322, c7329, c1798, c1789, c1805, c7326] c7330 unsat7330 (by rfl) a
  have h0 : Entails.eval a c7302 := derived7302 a h
  have h1 : Entails.eval a c7328 := derived7328 a h
  have h2 : Entails.eval a c7318 := derived7318 a h
  have h3 : Entails.eval a c7322 := derived7322 a h
  have h4 : Entails.eval a c7329 := derived7329 a h
  have h5 : Entails.eval a c1798 := h 1797 (by decide)
  have h6 : Entails.eval a c1789 := h 1788 (by decide)
  have h7 : Entails.eval a c1805 := h 1804 (by decide)
  have h8 : Entails.eval a c7326 := derived7326 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7331 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7331 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c399, some c404, some c380, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7331 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7331 : lratChecker f7331 p7331 = .success := by decide +kernel
theorem unsat7331 : Unsatisfiable (PosFin 65) f7331 := by
  apply lratCheckerSound f7331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7331
  · intro a ha; simp [p7331] at ha; subst a; trivial
  · exact checked7331
theorem derived7331 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7331 := by
  apply localUnsat_implies_entails f7331 [c399, c404, c380] c7331 unsat7331 (by rfl) a
  have h0 : Entails.eval a c399 := h 398 (by decide)
  have h1 : Entails.eval a c404 := h 403 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7332 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7332 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7328, some c7322, some c7302, some c7318, some c7331, some c7316, some c1798, some c1788, some c7330, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7332 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7332 : lratChecker f7332 p7332 = .success := by decide +kernel
theorem unsat7332 : Unsatisfiable (PosFin 65) f7332 := by
  apply lratCheckerSound f7332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7332
  · intro a ha; simp [p7332] at ha; subst a; trivial
  · exact checked7332
theorem derived7332 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7332 := by
  apply localUnsat_implies_entails f7332 [c7328, c7322, c7302, c7318, c7331, c7316, c1798, c1788, c7330] c7332 unsat7332 (by rfl) a
  have h0 : Entails.eval a c7328 := derived7328 a h
  have h1 : Entails.eval a c7322 := derived7322 a h
  have h2 : Entails.eval a c7302 := derived7302 a h
  have h3 : Entails.eval a c7318 := derived7318 a h
  have h4 : Entails.eval a c7331 := derived7331 a h
  have h5 : Entails.eval a c7316 := derived7316 a h
  have h6 : Entails.eval a c1798 := h 1797 (by decide)
  have h7 : Entails.eval a c1788 := h 1787 (by decide)
  have h8 : Entails.eval a c7330 := derived7330 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7333 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7333 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c397, some c393, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7333 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7333 : lratChecker f7333 p7333 = .success := by decide +kernel
theorem unsat7333 : Unsatisfiable (PosFin 65) f7333 := by
  apply lratCheckerSound f7333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7333
  · intro a ha; simp [p7333] at ha; subst a; trivial
  · exact checked7333
theorem derived7333 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7333 := by
  apply localUnsat_implies_entails f7333 [c397, c393] c7333 unsat7333 (by rfl) a
  have h0 : Entails.eval a c397 := h 396 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7334 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7334 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7333, some c1804, some c1789, some c1809, some c1815, some c1810, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7334 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7334 : lratChecker f7334 p7334 = .success := by decide +kernel
theorem unsat7334 : Unsatisfiable (PosFin 65) f7334 := by
  apply lratCheckerSound f7334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7334
  · intro a ha; simp [p7334] at ha; subst a; trivial
  · exact checked7334
theorem derived7334 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7334 := by
  apply localUnsat_implies_entails f7334 [c7333, c1804, c1789, c1809, c1815, c1810] c7334 unsat7334 (by rfl) a
  have h0 : Entails.eval a c7333 := derived7333 a h
  have h1 : Entails.eval a c1804 := h 1803 (by decide)
  have h2 : Entails.eval a c1789 := h 1788 (by decide)
  have h3 : Entails.eval a c1809 := h 1808 (by decide)
  have h4 : Entails.eval a c1815 := h 1814 (by decide)
  have h5 : Entails.eval a c1810 := h 1809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7335 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7335 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7316, some c403, some c415, some c381, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7335 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7335 : lratChecker f7335 p7335 = .success := by decide +kernel
theorem unsat7335 : Unsatisfiable (PosFin 65) f7335 := by
  apply lratCheckerSound f7335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7335
  · intro a ha; simp [p7335] at ha; subst a; trivial
  · exact checked7335
theorem derived7335 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7335 := by
  apply localUnsat_implies_entails f7335 [c7316, c403, c415, c381] c7335 unsat7335 (by rfl) a
  have h0 : Entails.eval a c7316 := derived7316 a h
  have h1 : Entails.eval a c403 := h 402 (by decide)
  have h2 : Entails.eval a c415 := h 414 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7336 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7336 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7334, some c7331, some c1804, some c1789, some c1805, some c1815, some c1810, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7336 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7336 : lratChecker f7336 p7336 = .success := by decide +kernel
theorem unsat7336 : Unsatisfiable (PosFin 65) f7336 := by
  apply lratCheckerSound f7336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7336
  · intro a ha; simp [p7336] at ha; subst a; trivial
  · exact checked7336
theorem derived7336 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7336 := by
  apply localUnsat_implies_entails f7336 [c7334, c7331, c1804, c1789, c1805, c1815, c1810] c7336 unsat7336 (by rfl) a
  have h0 : Entails.eval a c7334 := derived7334 a h
  have h1 : Entails.eval a c7331 := derived7331 a h
  have h2 : Entails.eval a c1804 := h 1803 (by decide)
  have h3 : Entails.eval a c1789 := h 1788 (by decide)
  have h4 : Entails.eval a c1805 := h 1804 (by decide)
  have h5 : Entails.eval a c1815 := h 1814 (by decide)
  have h6 : Entails.eval a c1810 := h 1809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7337 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7337 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7335, some c7336, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7337 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7337 : lratChecker f7337 p7337 = .success := by decide +kernel
theorem unsat7337 : Unsatisfiable (PosFin 65) f7337 := by
  apply lratCheckerSound f7337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7337
  · intro a ha; simp [p7337] at ha; subst a; trivial
  · exact checked7337
theorem derived7337 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7337 := by
  apply localUnsat_implies_entails f7337 [c7335, c7336] c7337 unsat7337 (by rfl) a
  have h0 : Entails.eval a c7335 := derived7335 a h
  have h1 : Entails.eval a c7336 := derived7336 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7338 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7338 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7302, some c7322, some c7328, some c7332, some c7337, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7338 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7338 : lratChecker f7338 p7338 = .success := by decide +kernel
theorem unsat7338 : Unsatisfiable (PosFin 65) f7338 := by
  apply lratCheckerSound f7338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7338
  · intro a ha; simp [p7338] at ha; subst a; trivial
  · exact checked7338
theorem derived7338 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7338 := by
  apply localUnsat_implies_entails f7338 [c7302, c7322, c7328, c7332, c7337] c7338 unsat7338 (by rfl) a
  have h0 : Entails.eval a c7302 := derived7302 a h
  have h1 : Entails.eval a c7322 := derived7322 a h
  have h2 : Entails.eval a c7328 := derived7328 a h
  have h3 : Entails.eval a c7332 := derived7332 a h
  have h4 : Entails.eval a c7337 := derived7337 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7339 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7339 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7192, some c7257, some c7338, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7339 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7339 : lratChecker f7339 p7339 = .success := by decide +kernel
theorem unsat7339 : Unsatisfiable (PosFin 65) f7339 := by
  apply lratCheckerSound f7339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7339
  · intro a ha; simp [p7339] at ha; subst a; trivial
  · exact checked7339
theorem derived7339 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7339 := by
  apply localUnsat_implies_entails f7339 [c7192, c7257, c7338] c7339 unsat7339 (by rfl) a
  have h0 : Entails.eval a c7192 := derived7192 a h
  have h1 : Entails.eval a c7257 := derived7257 a h
  have h2 : Entails.eval a c7338 := derived7338 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7340 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7340 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1276, some c1275, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7340 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7340 : lratChecker f7340 p7340 = .success := by decide +kernel
theorem unsat7340 : Unsatisfiable (PosFin 65) f7340 := by
  apply lratCheckerSound f7340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7340
  · intro a ha; simp [p7340] at ha; subst a; trivial
  · exact checked7340
theorem derived7340 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7340 := by
  apply localUnsat_implies_entails f7340 [c1276, c1275] c7340 unsat7340 (by rfl) a
  have h0 : Entails.eval a c1276 := h 1275 (by decide)
  have h1 : Entails.eval a c1275 := h 1274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7341 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨30, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7341 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c767, some c247, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7341 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7341 : lratChecker f7341 p7341 = .success := by decide +kernel
theorem unsat7341 : Unsatisfiable (PosFin 65) f7341 := by
  apply lratCheckerSound f7341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7341
  · intro a ha; simp [p7341] at ha; subst a; trivial
  · exact checked7341
theorem derived7341 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7341 := by
  apply localUnsat_implies_entails f7341 [c767, c247] c7341 unsat7341 (by rfl) a
  have h0 : Entails.eval a c767 := h 766 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7342 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7342 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c938, some c953, some c1556, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7342 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7342 : lratChecker f7342 p7342 = .success := by decide +kernel
theorem unsat7342 : Unsatisfiable (PosFin 65) f7342 := by
  apply lratCheckerSound f7342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7342
  · intro a ha; simp [p7342] at ha; subst a; trivial
  · exact checked7342
theorem derived7342 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7342 := by
  apply localUnsat_implies_entails f7342 [c938, c953, c1556] c7342 unsat7342 (by rfl) a
  have h0 : Entails.eval a c938 := h 937 (by decide)
  have h1 : Entails.eval a c953 := h 952 (by decide)
  have h2 : Entails.eval a c1556 := h 1555 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7343 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7343 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c941, some c956, some c1559, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7343 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7343 : lratChecker f7343 p7343 = .success := by decide +kernel
theorem unsat7343 : Unsatisfiable (PosFin 65) f7343 := by
  apply lratCheckerSound f7343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7343
  · intro a ha; simp [p7343] at ha; subst a; trivial
  · exact checked7343
theorem derived7343 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7343 := by
  apply localUnsat_implies_entails f7343 [c941, c956, c1559] c7343 unsat7343 (by rfl) a
  have h0 : Entails.eval a c941 := h 940 (by decide)
  have h1 : Entails.eval a c956 := h 955 (by decide)
  have h2 : Entails.eval a c1559 := h 1558 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7344 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7344 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c755, some c701, some c1424, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7344 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7344 : lratChecker f7344 p7344 = .success := by decide +kernel
theorem unsat7344 : Unsatisfiable (PosFin 65) f7344 := by
  apply lratCheckerSound f7344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7344
  · intro a ha; simp [p7344] at ha; subst a; trivial
  · exact checked7344
theorem derived7344 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7344 := by
  apply localUnsat_implies_entails f7344 [c755, c701, c1424] c7344 unsat7344 (by rfl) a
  have h0 : Entails.eval a c755 := h 754 (by decide)
  have h1 : Entails.eval a c701 := h 700 (by decide)
  have h2 : Entails.eval a c1424 := h 1423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7345 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7345 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7344, some c697, some c752, some c1421, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7345 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7345 : lratChecker f7345 p7345 = .success := by decide +kernel
theorem unsat7345 : Unsatisfiable (PosFin 65) f7345 := by
  apply lratCheckerSound f7345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7345
  · intro a ha; simp [p7345] at ha; subst a; trivial
  · exact checked7345
theorem derived7345 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7345 := by
  apply localUnsat_implies_entails f7345 [c7344, c697, c752, c1421] c7345 unsat7345 (by rfl) a
  have h0 : Entails.eval a c7344 := derived7344 a h
  have h1 : Entails.eval a c697 := h 696 (by decide)
  have h2 : Entails.eval a c752 := h 751 (by decide)
  have h3 : Entails.eval a c1421 := h 1420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7346 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7346 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1030, some c935, some c934, some c1052, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7346 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7346 : lratChecker f7346 p7346 = .success := by decide +kernel
theorem unsat7346 : Unsatisfiable (PosFin 65) f7346 := by
  apply lratCheckerSound f7346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7346
  · intro a ha; simp [p7346] at ha; subst a; trivial
  · exact checked7346
theorem derived7346 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7346 := by
  apply localUnsat_implies_entails f7346 [c1030, c935, c934, c1052] c7346 unsat7346 (by rfl) a
  have h0 : Entails.eval a c1030 := h 1029 (by decide)
  have h1 : Entails.eval a c935 := h 934 (by decide)
  have h2 : Entails.eval a c934 := h 933 (by decide)
  have h3 : Entails.eval a c1052 := h 1051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7347 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7347 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c185, some c196, some c186, some c205, some c188, some c258, some c791, some c2621, some c1830, some c1817, some c2543, some c2464, some c2522, some c2513, some c7346, some c6698, some c6699, some c211, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7347 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7347 : lratChecker f7347 p7347 = .success := by decide +kernel
theorem unsat7347 : Unsatisfiable (PosFin 65) f7347 := by
  apply lratCheckerSound f7347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7347
  · intro a ha; simp [p7347] at ha; subst a; trivial
  · exact checked7347
theorem derived7347 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7347 := by
  apply localUnsat_implies_entails f7347 [c185, c196, c186, c205, c188, c258, c791, c2621, c1830, c1817, c2543, c2464, c2522, c2513, c7346, c6698, c6699, c211] c7347 unsat7347 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c791 := h 790 (by decide)
  have h7 : Entails.eval a c2621 := h 2620 (by decide)
  have h8 : Entails.eval a c1830 := h 1829 (by decide)
  have h9 : Entails.eval a c1817 := h 1816 (by decide)
  have h10 : Entails.eval a c2543 := h 2542 (by decide)
  have h11 : Entails.eval a c2464 := h 2463 (by decide)
  have h12 : Entails.eval a c2522 := h 2521 (by decide)
  have h13 : Entails.eval a c2513 := h 2512 (by decide)
  have h14 : Entails.eval a c7346 := derived7346 a h
  have h15 : Entails.eval a c6698 := derived6698 a h
  have h16 : Entails.eval a c6699 := derived6699 a h
  have h17 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7348 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7348 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c185, some c7343, some c205, some c198, some c196, some c186, some c188, some c7347, some c1285, some c1341, some c1424, some c1961, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7348 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7348 : lratChecker f7348 p7348 = .success := by decide +kernel
theorem unsat7348 : Unsatisfiable (PosFin 65) f7348 := by
  apply lratCheckerSound f7348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7348
  · intro a ha; simp [p7348] at ha; subst a; trivial
  · exact checked7348
theorem derived7348 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7348 := by
  apply localUnsat_implies_entails f7348 [c185, c7343, c205, c198, c196, c186, c188, c7347, c1285, c1341, c1424, c1961] c7348 unsat7348 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c7343 := derived7343 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c7347 := derived7347 a h
  have h8 : Entails.eval a c1285 := h 1284 (by decide)
  have h9 : Entails.eval a c1341 := h 1340 (by decide)
  have h10 : Entails.eval a c1424 := h 1423 (by decide)
  have h11 : Entails.eval a c1961 := h 1960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7349 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7349 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c191, some c193, some c205, some c198, some c196, some c185, some c188, some c201, some c789, some c258, some c2623, some c2548, some c1840, some c1821, some c2527, some c2519, some c2465, some c7346, some c6698, some c6699, some c211, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7349 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7349 : lratChecker f7349 p7349 = .success := by decide +kernel
theorem unsat7349 : Unsatisfiable (PosFin 65) f7349 := by
  apply lratCheckerSound f7349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7349
  · intro a ha; simp [p7349] at ha; subst a; trivial
  · exact checked7349
theorem derived7349 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7349 := by
  apply localUnsat_implies_entails f7349 [c191, c193, c205, c198, c196, c185, c188, c201, c789, c258, c2623, c2548, c1840, c1821, c2527, c2519, c2465, c7346, c6698, c6699, c211] c7349 unsat7349 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c789 := h 788 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c2623 := h 2622 (by decide)
  have h11 : Entails.eval a c2548 := h 2547 (by decide)
  have h12 : Entails.eval a c1840 := h 1839 (by decide)
  have h13 : Entails.eval a c1821 := h 1820 (by decide)
  have h14 : Entails.eval a c2527 := h 2526 (by decide)
  have h15 : Entails.eval a c2519 := h 2518 (by decide)
  have h16 : Entails.eval a c2465 := h 2464 (by decide)
  have h17 : Entails.eval a c7346 := derived7346 a h
  have h18 : Entails.eval a c6698 := derived6698 a h
  have h19 : Entails.eval a c6699 := derived6699 a h
  have h20 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7350 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7350 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c191, some c7342, some c7343, some c193, some c205, some c185, some c188, some c198, some c196, some c186, some c7345, some c7348, some c7349, some c1284, some c1350, some c1423, some c1969, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7350 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked7350 : lratChecker f7350 p7350 = .success := by decide +kernel
theorem unsat7350 : Unsatisfiable (PosFin 65) f7350 := by
  apply lratCheckerSound f7350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7350
  · intro a ha; simp [p7350] at ha; subst a; trivial
  · exact checked7350
theorem derived7350 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7350 := by
  apply localUnsat_implies_entails f7350 [c191, c7342, c7343, c193, c205, c185, c188, c198, c196, c186, c7345, c7348, c7349, c1284, c1350, c1423, c1969] c7350 unsat7350 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c7342 := derived7342 a h
  have h2 : Entails.eval a c7343 := derived7343 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c7345 := derived7345 a h
  have h11 : Entails.eval a c7348 := derived7348 a h
  have h12 : Entails.eval a c7349 := derived7349 a h
  have h13 : Entails.eval a c1284 := h 1283 (by decide)
  have h14 : Entails.eval a c1350 := h 1349 (by decide)
  have h15 : Entails.eval a c1423 := h 1422 (by decide)
  have h16 : Entails.eval a c1969 := h 1968 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7351 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7351 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c939, some c954, some c1557, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7351 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7351 : lratChecker f7351 p7351 = .success := by decide +kernel
theorem unsat7351 : Unsatisfiable (PosFin 65) f7351 := by
  apply lratCheckerSound f7351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7351
  · intro a ha; simp [p7351] at ha; subst a; trivial
  · exact checked7351
theorem derived7351 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7351 := by
  apply localUnsat_implies_entails f7351 [c939, c954, c1557] c7351 unsat7351 (by rfl) a
  have h0 : Entails.eval a c939 := h 938 (by decide)
  have h1 : Entails.eval a c954 := h 953 (by decide)
  have h2 : Entails.eval a c1557 := h 1556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7352 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7352 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c226, some c217, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7352 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7352 : lratChecker f7352 p7352 = .success := by decide +kernel
theorem unsat7352 : Unsatisfiable (PosFin 65) f7352 := by
  apply lratCheckerSound f7352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7352
  · intro a ha; simp [p7352] at ha; subst a; trivial
  · exact checked7352
theorem derived7352 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7352 := by
  apply localUnsat_implies_entails f7352 [c226, c217] c7352 unsat7352 (by rfl) a
  have h0 : Entails.eval a c226 := h 225 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7353 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7353 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7138, some c193, some c198, some c205, some c202, some c175, some c7247, some c7351, some c7352, some c1430, some c1411, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7353 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7353 : lratChecker f7353 p7353 = .success := by decide +kernel
theorem unsat7353 : Unsatisfiable (PosFin 65) f7353 := by
  apply lratCheckerSound f7353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7353
  · intro a ha; simp [p7353] at ha; subst a; trivial
  · exact checked7353
theorem derived7353 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7353 := by
  apply localUnsat_implies_entails f7353 [c7138, c193, c198, c205, c202, c175, c7247, c7351, c7352, c1430, c1411] c7353 unsat7353 (by rfl) a
  have h0 : Entails.eval a c7138 := derived7138 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c7247 := derived7247 a h
  have h7 : Entails.eval a c7351 := derived7351 a h
  have h8 : Entails.eval a c7352 := derived7352 a h
  have h9 : Entails.eval a c1430 := h 1429 (by decide)
  have h10 : Entails.eval a c1411 := h 1410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7354 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7354 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c199, some c197, some c186, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7354 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7354 : lratChecker f7354 p7354 = .success := by decide +kernel
theorem unsat7354 : Unsatisfiable (PosFin 65) f7354 := by
  apply lratCheckerSound f7354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7354
  · intro a ha; simp [p7354] at ha; subst a; trivial
  · exact checked7354
theorem derived7354 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7354 := by
  apply localUnsat_implies_entails f7354 [c199, c197, c186] c7354 unsat7354 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7355 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7355 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c696, some c751, some c1422, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7355 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7355 : lratChecker f7355 p7355 = .success := by decide +kernel
theorem unsat7355 : Unsatisfiable (PosFin 65) f7355 := by
  apply lratCheckerSound f7355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7355
  · intro a ha; simp [p7355] at ha; subst a; trivial
  · exact checked7355
theorem derived7355 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7355 := by
  apply localUnsat_implies_entails f7355 [c696, c751, c1422] c7355 unsat7355 (by rfl) a
  have h0 : Entails.eval a c696 := h 695 (by decide)
  have h1 : Entails.eval a c751 := h 750 (by decide)
  have h2 : Entails.eval a c1422 := h 1421 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7356 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7356 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7350, some c7138, some c193, some c189, some c7354, some c198, some c7353, some c205, some c175, some c7247, some c180, some c7352, some c1420, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7356 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7356 : lratChecker f7356 p7356 = .success := by decide +kernel
theorem unsat7356 : Unsatisfiable (PosFin 65) f7356 := by
  apply lratCheckerSound f7356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7356
  · intro a ha; simp [p7356] at ha; subst a; trivial
  · exact checked7356
theorem derived7356 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7356 := by
  apply localUnsat_implies_entails f7356 [c7350, c7138, c193, c189, c7354, c198, c7353, c205, c175, c7247, c180, c7352, c1420] c7356 unsat7356 (by rfl) a
  have h0 : Entails.eval a c7350 := derived7350 a h
  have h1 : Entails.eval a c7138 := derived7138 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c7354 := derived7354 a h
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c7353 := derived7353 a h
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c7247 := derived7247 a h
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c7352 := derived7352 a h
  have h12 : Entails.eval a c1420 := h 1419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7357 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨10, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7357 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c2283, some c1325, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7357 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7357 : lratChecker f7357 p7357 = .success := by decide +kernel
theorem unsat7357 : Unsatisfiable (PosFin 65) f7357 := by
  apply lratCheckerSound f7357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7357
  · intro a ha; simp [p7357] at ha; subst a; trivial
  · exact checked7357
theorem derived7357 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7357 := by
  apply localUnsat_implies_entails f7357 [c1171, c2283, c1325] c7357 unsat7357 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c2283 := h 2282 (by decide)
  have h2 : Entails.eval a c1325 := h 1324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7358 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨30, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7358 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c767, some c749, some c268, some c7357, some c2280, some c1176, some c1329, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7358 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7358 : lratChecker f7358 p7358 = .success := by decide +kernel
theorem unsat7358 : Unsatisfiable (PosFin 65) f7358 := by
  apply lratCheckerSound f7358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7358
  · intro a ha; simp [p7358] at ha; subst a; trivial
  · exact checked7358
theorem derived7358 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7358 := by
  apply localUnsat_implies_entails f7358 [c767, c749, c268, c7357, c2280, c1176, c1329] c7358 unsat7358 (by rfl) a
  have h0 : Entails.eval a c767 := h 766 (by decide)
  have h1 : Entails.eval a c749 := h 748 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c7357 := derived7357 a h
  have h4 : Entails.eval a c2280 := h 2279 (by decide)
  have h5 : Entails.eval a c1176 := h 1175 (by decide)
  have h6 : Entails.eval a c1329 := h 1328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7359 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7359 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7226, some c7259, some c7236, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7359 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7359 : lratChecker f7359 p7359 = .success := by decide +kernel
theorem unsat7359 : Unsatisfiable (PosFin 65) f7359 := by
  apply lratCheckerSound f7359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7359
  · intro a ha; simp [p7359] at ha; subst a; trivial
  · exact checked7359
theorem derived7359 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7359 := by
  apply localUnsat_implies_entails f7359 [c7226, c7259, c7236] c7359 unsat7359 (by rfl) a
  have h0 : Entails.eval a c7226 := derived7226 a h
  have h1 : Entails.eval a c7259 := derived7259 a h
  have h2 : Entails.eval a c7236 := derived7236 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7360 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7360 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7291, some c7297, some c7237, some c273, some c1721, some c7273, some c7204, some c1754, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7360 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7360 : lratChecker f7360 p7360 = .success := by decide +kernel
theorem unsat7360 : Unsatisfiable (PosFin 65) f7360 := by
  apply lratCheckerSound f7360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7360
  · intro a ha; simp [p7360] at ha; subst a; trivial
  · exact checked7360
theorem derived7360 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7360 := by
  apply localUnsat_implies_entails f7360 [c7291, c7297, c7237, c273, c1721, c7273, c7204, c1754] c7360 unsat7360 (by rfl) a
  have h0 : Entails.eval a c7291 := derived7291 a h
  have h1 : Entails.eval a c7297 := derived7297 a h
  have h2 : Entails.eval a c7237 := derived7237 a h
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c1721 := h 1720 (by decide)
  have h5 : Entails.eval a c7273 := derived7273 a h
  have h6 : Entails.eval a c7204 := derived7204 a h
  have h7 : Entails.eval a c1754 := h 1753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7361 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7361 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7360, some c7291, some c7297, some c7237, some c7359, some c261, some c267, some c247, some c7358, some c7229, some c7205, some c7283, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7361 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7361 : lratChecker f7361 p7361 = .success := by decide +kernel
theorem unsat7361 : Unsatisfiable (PosFin 65) f7361 := by
  apply lratCheckerSound f7361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7361
  · intro a ha; simp [p7361] at ha; subst a; trivial
  · exact checked7361
theorem derived7361 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7361 := by
  apply localUnsat_implies_entails f7361 [c7360, c7291, c7297, c7237, c7359, c261, c267, c247, c7358, c7229, c7205, c7283] c7361 unsat7361 (by rfl) a
  have h0 : Entails.eval a c7360 := derived7360 a h
  have h1 : Entails.eval a c7291 := derived7291 a h
  have h2 : Entails.eval a c7297 := derived7297 a h
  have h3 : Entails.eval a c7237 := derived7237 a h
  have h4 : Entails.eval a c7359 := derived7359 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c7358 := derived7358 a h
  have h9 : Entails.eval a c7229 := derived7229 a h
  have h10 : Entails.eval a c7205 := derived7205 a h
  have h11 : Entails.eval a c7283 := derived7283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7362 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7362 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c697, some c752, some c1423, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7362 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7362 : lratChecker f7362 p7362 = .success := by decide +kernel
theorem unsat7362 : Unsatisfiable (PosFin 65) f7362 := by
  apply lratCheckerSound f7362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7362
  · intro a ha; simp [p7362] at ha; subst a; trivial
  · exact checked7362
theorem derived7362 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7362 := by
  apply localUnsat_implies_entails f7362 [c697, c752, c1423] c7362 unsat7362 (by rfl) a
  have h0 : Entails.eval a c697 := h 696 (by decide)
  have h1 : Entails.eval a c752 := h 751 (by decide)
  have h2 : Entails.eval a c1423 := h 1422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7363 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7363 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7291, some c7297, some c7361, some c7362, some c1580, some c1738, some c1792, some c2024, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7363 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7363 : lratChecker f7363 p7363 = .success := by decide +kernel
theorem unsat7363 : Unsatisfiable (PosFin 65) f7363 := by
  apply lratCheckerSound f7363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7363
  · intro a ha; simp [p7363] at ha; subst a; trivial
  · exact checked7363
theorem derived7363 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7363 := by
  apply localUnsat_implies_entails f7363 [c7291, c7297, c7361, c7362, c1580, c1738, c1792, c2024] c7363 unsat7363 (by rfl) a
  have h0 : Entails.eval a c7291 := derived7291 a h
  have h1 : Entails.eval a c7297 := derived7297 a h
  have h2 : Entails.eval a c7361 := derived7361 a h
  have h3 : Entails.eval a c7362 := derived7362 a h
  have h4 : Entails.eval a c1580 := h 1579 (by decide)
  have h5 : Entails.eval a c1738 := h 1737 (by decide)
  have h6 : Entails.eval a c1792 := h 1791 (by decide)
  have h7 : Entails.eval a c2024 := h 2023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7364 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7364 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c273, some c753, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7364 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7364 : lratChecker f7364 p7364 = .success := by decide +kernel
theorem unsat7364 : Unsatisfiable (PosFin 65) f7364 := by
  apply lratCheckerSound f7364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7364
  · intro a ha; simp [p7364] at ha; subst a; trivial
  · exact checked7364
theorem derived7364 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7364 := by
  apply localUnsat_implies_entails f7364 [c273, c753] c7364 unsat7364 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c753 := h 752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7365 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7365 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c219, some c1765, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7365 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7365 : lratChecker f7365 p7365 = .success := by decide +kernel
theorem unsat7365 : Unsatisfiable (PosFin 65) f7365 := by
  apply lratCheckerSound f7365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7365
  · intro a ha; simp [p7365] at ha; subst a; trivial
  · exact checked7365
theorem derived7365 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7365 := by
  apply localUnsat_implies_entails f7365 [c219, c1765] c7365 unsat7365 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c1765 := h 1764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7366 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7366 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7237, some c7365, some c7226, some c7204, some c7273, some c1414, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7366 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7366 : lratChecker f7366 p7366 = .success := by decide +kernel
theorem unsat7366 : Unsatisfiable (PosFin 65) f7366 := by
  apply lratCheckerSound f7366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7366
  · intro a ha; simp [p7366] at ha; subst a; trivial
  · exact checked7366
theorem derived7366 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7366 := by
  apply localUnsat_implies_entails f7366 [c7237, c7365, c7226, c7204, c7273, c1414] c7366 unsat7366 (by rfl) a
  have h0 : Entails.eval a c7237 := derived7237 a h
  have h1 : Entails.eval a c7365 := derived7365 a h
  have h2 : Entails.eval a c7226 := derived7226 a h
  have h3 : Entails.eval a c7204 := derived7204 a h
  have h4 : Entails.eval a c7273 := derived7273 a h
  have h5 : Entails.eval a c1414 := h 1413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7367 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7367 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c273, some c790, some c7364, some c1791, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7367 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7367 : lratChecker f7367 p7367 = .success := by decide +kernel
theorem unsat7367 : Unsatisfiable (PosFin 65) f7367 := by
  apply lratCheckerSound f7367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7367
  · intro a ha; simp [p7367] at ha; subst a; trivial
  · exact checked7367
theorem derived7367 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7367 := by
  apply localUnsat_implies_entails f7367 [c273, c790, c7364, c1791] c7367 unsat7367 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c790 := h 789 (by decide)
  have h2 : Entails.eval a c7364 := derived7364 a h
  have h3 : Entails.eval a c1791 := h 1790 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7368 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7368 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7237, some c7363, some c7366, some c251, some c253, some c7367, some c752, some c789, some c1792, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7368 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7368 : lratChecker f7368 p7368 = .success := by decide +kernel
theorem unsat7368 : Unsatisfiable (PosFin 65) f7368 := by
  apply lratCheckerSound f7368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7368
  · intro a ha; simp [p7368] at ha; subst a; trivial
  · exact checked7368
theorem derived7368 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7368 := by
  apply localUnsat_implies_entails f7368 [c7237, c7363, c7366, c251, c253, c7367, c752, c789, c1792] c7368 unsat7368 (by rfl) a
  have h0 : Entails.eval a c7237 := derived7237 a h
  have h1 : Entails.eval a c7363 := derived7363 a h
  have h2 : Entails.eval a c7366 := derived7366 a h
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c7367 := derived7367 a h
  have h6 : Entails.eval a c752 := h 751 (by decide)
  have h7 : Entails.eval a c789 := h 788 (by decide)
  have h8 : Entails.eval a c1792 := h 1791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7369 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7369 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c273, some c755, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7369 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7369 : lratChecker f7369 p7369 = .success := by decide +kernel
theorem unsat7369 : Unsatisfiable (PosFin 65) f7369 := by
  apply lratCheckerSound f7369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7369
  · intro a ha; simp [p7369] at ha; subst a; trivial
  · exact checked7369
theorem derived7369 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7369 := by
  apply localUnsat_implies_entails f7369 [c273, c755] c7369 unsat7369 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c755 := h 754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7370 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7370 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1287, some c1352, some c127, some c89, some c2193, some c1992, some c1656, some c2679, some c151, some c3114, some c3117, some c3111, some c3115, some c94, some c3112, some c3118, some c3103, some c3098, some c3116, some c3094, some c6747, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7370 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked7370 : lratChecker f7370 p7370 = .success := by decide +kernel
theorem unsat7370 : Unsatisfiable (PosFin 65) f7370 := by
  apply lratCheckerSound f7370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7370
  · intro a ha; simp [p7370] at ha; subst a; trivial
  · exact checked7370
theorem derived7370 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7370 := by
  apply localUnsat_implies_entails f7370 [c1287, c1352, c127, c89, c2193, c1992, c1656, c2679, c151, c3114, c3117, c3111, c3115, c94, c3112, c3118, c3103, c3098, c3116, c3094, c6747] c7370 unsat7370 (by rfl) a
  have h0 : Entails.eval a c1287 := h 1286 (by decide)
  have h1 : Entails.eval a c1352 := h 1351 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c2193 := h 2192 (by decide)
  have h5 : Entails.eval a c1992 := h 1991 (by decide)
  have h6 : Entails.eval a c1656 := h 1655 (by decide)
  have h7 : Entails.eval a c2679 := h 2678 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c3114 := h 3113 (by decide)
  have h10 : Entails.eval a c3117 := h 3116 (by decide)
  have h11 : Entails.eval a c3111 := h 3110 (by decide)
  have h12 : Entails.eval a c3115 := h 3114 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c3112 := h 3111 (by decide)
  have h15 : Entails.eval a c3118 := h 3117 (by decide)
  have h16 : Entails.eval a c3103 := h 3102 (by decide)
  have h17 : Entails.eval a c3098 := h 3097 (by decide)
  have h18 : Entails.eval a c3116 := h 3115 (by decide)
  have h19 : Entails.eval a c3094 := h 3093 (by decide)
  have h20 : Entails.eval a c6747 := derived6747 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7371 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7371 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7368, some c7369, some c7370, some c1624, some c1719, some c1050, some c131, some c1564, some c160, some c3335, some c3332, some c3333, some c3331, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7371 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7371 : lratChecker f7371 p7371 = .success := by decide +kernel
theorem unsat7371 : Unsatisfiable (PosFin 65) f7371 := by
  apply lratCheckerSound f7371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7371
  · intro a ha; simp [p7371] at ha; subst a; trivial
  · exact checked7371
theorem derived7371 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7371 := by
  apply localUnsat_implies_entails f7371 [c7339, c7356, c7368, c7369, c7370, c1624, c1719, c1050, c131, c1564, c160, c3335, c3332, c3333, c3331] c7371 unsat7371 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7368 := derived7368 a h
  have h3 : Entails.eval a c7369 := derived7369 a h
  have h4 : Entails.eval a c7370 := derived7370 a h
  have h5 : Entails.eval a c1624 := h 1623 (by decide)
  have h6 : Entails.eval a c1719 := h 1718 (by decide)
  have h7 : Entails.eval a c1050 := h 1049 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c1564 := h 1563 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c3335 := h 3334 (by decide)
  have h12 : Entails.eval a c3332 := h 3331 (by decide)
  have h13 : Entails.eval a c3333 := h 3332 (by decide)
  have h14 : Entails.eval a c3331 := h 3330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7372 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7372 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c273, some c793, some c1793, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7372 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7372 : lratChecker f7372 p7372 = .success := by decide +kernel
theorem unsat7372 : Unsatisfiable (PosFin 65) f7372 := by
  apply lratCheckerSound f7372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7372
  · intro a ha; simp [p7372] at ha; subst a; trivial
  · exact checked7372
theorem derived7372 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7372 := by
  apply localUnsat_implies_entails f7372 [c273, c793, c1793] c7372 unsat7372 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c793 := h 792 (by decide)
  have h2 : Entails.eval a c1793 := h 1792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7373 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7373 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1793, some c1740, some c2026, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p7373 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7373 : lratChecker f7373 p7373 = .success := by decide +kernel
theorem unsat7373 : Unsatisfiable (PosFin 65) f7373 := by
  apply lratCheckerSound f7373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7373
  · intro a ha; simp [p7373] at ha; subst a; trivial
  · exact checked7373
theorem derived7373 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7373 := by
  apply localUnsat_implies_entails f7373 [c1793, c1740, c2026] c7373 unsat7373 (by rfl) a
  have h0 : Entails.eval a c1793 := h 1792 (by decide)
  have h1 : Entails.eval a c1740 := h 1739 (by decide)
  have h2 : Entails.eval a c2026 := h 2025 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7374 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7374 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7368, some c7371, some c7206, some c7372, some c7373, some c1719, some c1050, some c1748, some c1564, some c2052, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7374 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7374 : lratChecker f7374 p7374 = .success := by decide +kernel
theorem unsat7374 : Unsatisfiable (PosFin 65) f7374 := by
  apply lratCheckerSound f7374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7374
  · intro a ha; simp [p7374] at ha; subst a; trivial
  · exact checked7374
theorem derived7374 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7374 := by
  apply localUnsat_implies_entails f7374 [c7339, c7356, c7368, c7371, c7206, c7372, c7373, c1719, c1050, c1748, c1564, c2052] c7374 unsat7374 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7368 := derived7368 a h
  have h3 : Entails.eval a c7371 := derived7371 a h
  have h4 : Entails.eval a c7206 := derived7206 a h
  have h5 : Entails.eval a c7372 := derived7372 a h
  have h6 : Entails.eval a c7373 := derived7373 a h
  have h7 : Entails.eval a c1719 := h 1718 (by decide)
  have h8 : Entails.eval a c1050 := h 1049 (by decide)
  have h9 : Entails.eval a c1748 := h 1747 (by decide)
  have h10 : Entails.eval a c1564 := h 1563 (by decide)
  have h11 : Entails.eval a c2052 := h 2051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7375 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7375 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1580, some c1738, some c1790, some c2024, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7375 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7375 : lratChecker f7375 p7375 = .success := by decide +kernel
theorem unsat7375 : Unsatisfiable (PosFin 65) f7375 := by
  apply lratCheckerSound f7375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7375
  · intro a ha; simp [p7375] at ha; subst a; trivial
  · exact checked7375
theorem derived7375 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7375 := by
  apply localUnsat_implies_entails f7375 [c1580, c1738, c1790, c2024] c7375 unsat7375 (by rfl) a
  have h0 : Entails.eval a c1580 := h 1579 (by decide)
  have h1 : Entails.eval a c1738 := h 1737 (by decide)
  have h2 : Entails.eval a c1790 := h 1789 (by decide)
  have h3 : Entails.eval a c2024 := h 2023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7376 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7376 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7339, some c7356, some c7374, some c7362, some c7375, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7376 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7376 : lratChecker f7376 p7376 = .success := by decide +kernel
theorem unsat7376 : Unsatisfiable (PosFin 65) f7376 := by
  apply lratCheckerSound f7376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7376
  · intro a ha; simp [p7376] at ha; subst a; trivial
  · exact checked7376
theorem derived7376 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7376 := by
  apply localUnsat_implies_entails f7376 [c7339, c7356, c7374, c7362, c7375] c7376 unsat7376 (by rfl) a
  have h0 : Entails.eval a c7339 := derived7339 a h
  have h1 : Entails.eval a c7356 := derived7356 a h
  have h2 : Entails.eval a c7374 := derived7374 a h
  have h3 : Entails.eval a c7362 := derived7362 a h
  have h4 : Entails.eval a c7375 := derived7375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7377 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7377 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7217, some c7245, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p7377 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7377 : lratChecker f7377 p7377 = .success := by decide +kernel
theorem unsat7377 : Unsatisfiable (PosFin 65) f7377 := by
  apply lratCheckerSound f7377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7377
  · intro a ha; simp [p7377] at ha; subst a; trivial
  · exact checked7377
theorem derived7377 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7377 := by
  apply localUnsat_implies_entails f7377 [c7217, c7245] c7377 unsat7377 (by rfl) a
  have h0 : Entails.eval a c7217 := derived7217 a h
  have h1 : Entails.eval a c7245 := derived7245 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7378 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7378 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7247, some c755, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7378 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7378 : lratChecker f7378 p7378 = .success := by decide +kernel
theorem unsat7378 : Unsatisfiable (PosFin 65) f7378 := by
  apply lratCheckerSound f7378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7378
  · intro a ha; simp [p7378] at ha; subst a; trivial
  · exact checked7378
theorem derived7378 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7378 := by
  apply localUnsat_implies_entails f7378 [c7247, c755] c7378 unsat7378 (by rfl) a
  have h0 : Entails.eval a c7247 := derived7247 a h
  have h1 : Entails.eval a c755 := h 754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7379 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7379 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1292, some c1290, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7379 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7379 : lratChecker f7379 p7379 = .success := by decide +kernel
theorem unsat7379 : Unsatisfiable (PosFin 65) f7379 := by
  apply lratCheckerSound f7379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7379
  · intro a ha; simp [p7379] at ha; subst a; trivial
  · exact checked7379
theorem derived7379 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7379 := by
  apply localUnsat_implies_entails f7379 [c1292, c1290] c7379 unsat7379 (by rfl) a
  have h0 : Entails.eval a c1292 := h 1291 (by decide)
  have h1 : Entails.eval a c1290 := h 1289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7380 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨55, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7380 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3150, some c3152, some c3148, some c3146, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7380 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7380 : lratChecker f7380 p7380 = .success := by decide +kernel
theorem unsat7380 : Unsatisfiable (PosFin 65) f7380 := by
  apply lratCheckerSound f7380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7380
  · intro a ha; simp [p7380] at ha; subst a; trivial
  · exact checked7380
theorem derived7380 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7380 := by
  apply localUnsat_implies_entails f7380 [c3150, c3152, c3148, c3146] c7380 unsat7380 (by rfl) a
  have h0 : Entails.eval a c3150 := h 3149 (by decide)
  have h1 : Entails.eval a c3152 := h 3151 (by decide)
  have h2 : Entails.eval a c3148 := h 3147 (by decide)
  have h3 : Entails.eval a c3146 := h 3145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7380

end CochromaticTwenty.Certificates.FixedCore1
