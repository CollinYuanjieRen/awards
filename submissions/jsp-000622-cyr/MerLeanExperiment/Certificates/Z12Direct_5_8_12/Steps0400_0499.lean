import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0300_0399

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1317 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c803, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1317 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 31) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c1179, c803] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c803 := h 802 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1318 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c825, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1318 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 31) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c1179, c825] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c825 := h 824 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1319 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c826, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1319 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 31) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c1179, c826] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c826 := h 825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1320 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c827, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 31) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c1179, c827] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c827 := h 826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1321 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c828, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 31) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c1179, c828] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c828 := h 827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1322 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c829, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1322 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 31) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1179, c829] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c829 := h 828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1323 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c830, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1323 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 31) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1179, c830] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c830 := h 829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1324 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c831, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1324 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 31) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1179, c831] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c831 := h 830 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1325 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨21, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c835, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 31) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c1179, c835] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c835 := h 834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1326 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c838, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1326 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 31) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c1179, c838] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c838 := h 837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1327 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c6, some c310, some c1251, some c1204, some c483, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1327 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 31) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c6, c310, c1251, c1204, c483] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c483 := h 482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c327, some c1197, some c1238, some c33, some c1327, some c1208, some c393, some c262, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1328 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 31) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c327, c1197, c1238, c33, c1327, c1208, c393, c262] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c327 := h 326 (by decide)
  have h1 : Entails.eval a c1197 := derived1197 a h
  have h2 : Entails.eval a c1238 := derived1238 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c1327 := derived1327 a h
  have h5 : Entails.eval a c1208 := derived1208 a h
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c50, some c35, some c69, some c12, some c33, some c1261, some c228, some c515, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1329 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 31) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c50, c35, c69, c12, c33, c1261, c228, c515] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c1261 := derived1261 a h
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c515 := h 514 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1329, some c1162, some c1327, some c33, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1330 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 31) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c1329, c1162, c1327, c33] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c1162 := derived1162 a h
  have h2 : Entails.eval a c1327 := derived1327 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1196, some c1197, some c1202, some c327, some c1330, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 31) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1196, c1197, c1202, c327, c1330] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1197 := derived1197 a h
  have h2 : Entails.eval a c1202 := derived1202 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c1330 := derived1330 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1205, some c343, some c1251, some c1257, some c1318, some c1297, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1332 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 31) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c1205, c343, c1251, c1257, c1318, c1297] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  have h3 : Entails.eval a c1257 := derived1257 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c1297 := derived1297 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1331, some c906, some c1243, some c309, some c784, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1333 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 31) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c1331, c906, c1243, c309, c784] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c906 := h 905 (by decide)
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c784 := h 783 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1331, some c1205, some c343, some c1204, some c1332, some c1333, some c1278, some c18, some c487, some c44, some c235, some c1022, some c32, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 31) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c1331, c1205, c343, c1204, c1332, c1333, c1278, c18, c487, c44, c235, c1022, c32] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1333 := derived1333 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c487 := h 486 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c1022 := derived1022 a h
  have h12 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c719, some c1275, some c881, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1335 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 31) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c719, c1275, c881] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c719 := h 718 (by decide)
  have h1 : Entails.eval a c1275 := derived1275 a h
  have h2 : Entails.eval a c881 := h 880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1331, some c1334, some c327, some c28, some c268, some c1335, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1336 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 31) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1331, c1334, c327, c28, c268, c1335] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c1334 := derived1334 a h
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1335 := derived1335 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1336, some c1331, some c1335, some c28, some c9, some c1278, some c30, some c1322, some c906, some c312, some c1207, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1337 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 31) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c1336, c1331, c1335, c28, c9, c1278, c30, c1322, c906, c312, c1207] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c1336 := derived1336 a h
  have h1 : Entails.eval a c1331 := derived1331 a h
  have h2 : Entails.eval a c1335 := derived1335 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1278 := derived1278 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1322 := derived1322 a h
  have h8 : Entails.eval a c906 := h 905 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  have h10 : Entails.eval a c1207 := derived1207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1337, some c1336, some c1331, some c28, some c9, some c1205, some c343, some c235, some c487, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1338 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 31) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1337, c1336, c1331, c28, c9, c1205, c343, c235, c487] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1337 := derived1337 a h
  have h1 : Entails.eval a c1336 := derived1336 a h
  have h2 : Entails.eval a c1331 := derived1331 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1205 := derived1205 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c235 := h 234 (by decide)
  have h8 : Entails.eval a c487 := h 486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1234, some c1205, some c1243, some c343, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1339 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 31) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1234, c1205, c1243, c343] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1234 := derived1234 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1331, some c1336, some c1337, some c1338, some c1339, some c268, some c213, some c1197, some c50, some c343, some c1243, some c24, some c1161, some c507, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1340 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 31) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1331, c1336, c1337, c1338, c1339, c268, c213, c1197, c50, c343, c1243, c24, c1161, c507] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c1336 := derived1336 a h
  have h2 : Entails.eval a c1337 := derived1337 a h
  have h3 : Entails.eval a c1338 := derived1338 a h
  have h4 : Entails.eval a c1339 := derived1339 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c1197 := derived1197 a h
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c1243 := derived1243 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c1161 := derived1161 a h
  have h13 : Entails.eval a c507 := h 506 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1287, some c308, some c1326, some c1283, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1341 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 31) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c1340, c1287, c308, c1326, c1283] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c1326 := derived1326 a h
  have h4 : Entails.eval a c1283 := derived1283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c213, some c26, some c1341, some c1243, some c29, some c205, some c284, some c711, some c303, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1342 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 31) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c1340, c213, c26, c1341, c1243, c29, c205, c284, c711, c303] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c213 := h 212 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c1341 := derived1341 a h
  have h4 : Entails.eval a c1243 := derived1243 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c711 := h 710 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1342, some c1234, some c1205, some c1243, some c29, some c284, some c1295, some c1284, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1343 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 31) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c1340, c1342, c1234, c1205, c1243, c29, c284, c1295, c1284] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1342 := derived1342 a h
  have h2 : Entails.eval a c1234 := derived1234 a h
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1243 := derived1243 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c1295 := derived1295 a h
  have h8 : Entails.eval a c1284 := derived1284 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1243, some c29, some c284, some c1295, some c1284, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1344 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 31) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1340, c1243, c29, c284, c1295, c1284] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1243 := derived1243 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c1295 := derived1295 a h
  have h5 : Entails.eval a c1284 := derived1284 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1205, some c1344, some c1287, some c1284, some c1302, some c53, some c1281, some c309, some c1326, some c1283, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1345 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 31) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c1340, c1205, c1344, c1287, c1284, c1302, c53, c1281, c309, c1326, c1283] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1344 := derived1344 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1284 := derived1284 a h
  have h5 : Entails.eval a c1302 := derived1302 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c1281 := derived1281 a h
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c1283 := derived1283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1343, some c1345, some c327, some c1340, some c1287, some c309, some c1326, some c1283, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1346 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 31) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1343, c1345, c327, c1340, c1287, c309, c1326, c1283] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1343 := derived1343 a h
  have h1 : Entails.eval a c1345 := derived1345 a h
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c1326 := derived1326 a h
  have h7 : Entails.eval a c1283 := derived1283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1343, some c1345, some c327, some c268, some c1346, some c1344, some c1209, some c747, some c1227, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1347 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 31) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c1340, c1343, c1345, c327, c268, c1346, c1344, c1209, c747, c1227] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1343 := derived1343 a h
  have h2 : Entails.eval a c1345 := derived1345 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1346 := derived1346 a h
  have h6 : Entails.eval a c1344 := derived1344 a h
  have h7 : Entails.eval a c1209 := derived1209 a h
  have h8 : Entails.eval a c747 := h 746 (by decide)
  have h9 : Entails.eval a c1227 := derived1227 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c28, some c1205, some c1340, some c4, some c2, some c1203, some c1295, some c284, some c848, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1348 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 31) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c28, c1205, c1340, c4, c2, c1203, c1295, c284, c848] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1203 := derived1203 a h
  have h6 : Entails.eval a c1295 := derived1295 a h
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c848 := h 847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1204, some c347, some c166, some c256, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1349 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 31) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c1204, c347, c166, c256] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c1204 := derived1204 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1347, some c28, some c1205, some c1340, some c1348, some c1349, some c29, some c284, some c1295, some c1284, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1350 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 31) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c1347, c28, c1205, c1340, c1348, c1349, c29, c284, c1295, c1284] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c1347 := derived1347 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1349 := derived1349 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c1295 := derived1295 a h
  have h9 : Entails.eval a c1284 := derived1284 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1347, some c28, some c1205, some c1350, some c1287, some c755, some c5, some c53, some c1203, some c907, some c191, some c84, some c137, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1351 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 31) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1340, c1347, c28, c1205, c1350, c1287, c755, c5, c53, c1203, c907, c191, c84, c137] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1347 := derived1347 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1350 := derived1350 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c755 := h 754 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c1203 := derived1203 a h
  have h10 : Entails.eval a c907 := h 906 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1351, some c1238, some c1340, some c1287, some c9, some c1217, some c1328, some c1227, some c1248, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1352 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 31) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c1351, c1238, c1340, c1287, c9, c1217, c1328, c1227, c1248] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1238 := derived1238 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1217 := derived1217 a h
  have h6 : Entails.eval a c1328 := derived1328 a h
  have h7 : Entails.eval a c1227 := derived1227 a h
  have h8 : Entails.eval a c1248 := derived1248 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1351, some c1340, some c28, some c1205, some c1352, some c1348, some c1328, some c1236, some c11, some c1204, some c236, some c1203, some c867, some c191, some c64, some c714, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1353 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 31) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1351, c1340, c28, c1205, c1352, c1348, c1328, c1236, c11, c1204, c236, c1203, c867, c191, c64, c714] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1340 := derived1340 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1352 := derived1352 a h
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c1328 := derived1328 a h
  have h7 : Entails.eval a c1236 := derived1236 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c1204 := derived1204 a h
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c1203 := derived1203 a h
  have h12 : Entails.eval a c867 := h 866 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c714 := h 713 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1351, some c1236, some c1197, some c1353, some c1204, some c236, some c1200, some c64, some c237, some c1244, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1354 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 31) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c1351, c1236, c1197, c1353, c1204, c236, c1200, c64, c237, c1244] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1236 := derived1236 a h
  have h2 : Entails.eval a c1197 := derived1197 a h
  have h3 : Entails.eval a c1353 := derived1353 a h
  have h4 : Entails.eval a c1204 := derived1204 a h
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c1200 := derived1200 a h
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c1244 := derived1244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1353, some c1351, some c1340, some c1236, some c1354, some c213, some c50, some c24, some c256, some c166, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1355 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 31) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1353, c1351, c1340, c1236, c1354, c213, c50, c24, c256, c166] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1353 := derived1353 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1236 := derived1236 a h
  have h4 : Entails.eval a c1354 := derived1354 a h
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1351, some c1197, some c1355, some c1330, some c327, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1356 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 31) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c1351, c1197, c1355, c1330, c327] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1197 := derived1197 a h
  have h2 : Entails.eval a c1355 := derived1355 a h
  have h3 : Entails.eval a c1330 := derived1330 a h
  have h4 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1356, some c1353, some c1340, some c17, some c1227, some c166, some c569, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1357 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 31) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c1356, c1353, c1340, c17, c1227, c166, c569] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c1356 := derived1356 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1227 := derived1227 a h
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c569 := h 568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1356, some c1353, some c1340, some c17, some c1357, some c1227, some c896, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1358 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 31) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c1356, c1353, c1340, c17, c1357, c1227, c896] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c1356 := derived1356 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1227 := derived1227 a h
  have h6 : Entails.eval a c896 := h 895 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1356, some c1351, some c1340, some c268, some c1358, some c558, some c1162, some c328, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1359 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 31) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c1356, c1351, c1340, c268, c1358, c558, c1162, c328] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c1356 := derived1356 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1358 := derived1358 a h
  have h5 : Entails.eval a c558 := h 557 (by decide)
  have h6 : Entails.eval a c1162 := derived1162 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c232, some c1203, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 31) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c29, c232, c1203] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1356, some c1351, some c1340, some c1205, some c1360, some c346, some c1204, some c69, some c110, some c1280, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1361 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 31) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c1356, c1351, c1340, c1205, c1360, c346, c1204, c69, c110, c1280] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c1356 := derived1356 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1360 := derived1360 a h
  have h5 : Entails.eval a c346 := h 345 (by decide)
  have h6 : Entails.eval a c1204 := derived1204 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1280 := derived1280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1351, some c1356, some c1361, some c268, some c1359, some c1358, some c1236, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1362 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 31) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c1351, c1356, c1361, c268, c1359, c1358, c1236] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c1351 := derived1351 a h
  have h1 : Entails.eval a c1356 := derived1356 a h
  have h2 : Entails.eval a c1361 := derived1361 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1359 := derived1359 a h
  have h5 : Entails.eval a c1358 := derived1358 a h
  have h6 : Entails.eval a c1236 := derived1236 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1362, some c1351, some c1340, some c1236, some c8, some c327, some c328, some c309, some c1208, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1363 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 31) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1362, c1351, c1340, c1236, c8, c327, c328, c309, c1208] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c1340 := derived1340 a h
  have h3 : Entails.eval a c1236 := derived1236 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c1208 := derived1208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1362, some c1353, some c1351, some c1340, some c327, some c309, some c268, some c1208, some c1277, some c328, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1364 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 31) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c1362, c1353, c1351, c1340, c327, c309, c268, c1208, c1277, c328] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c1351 := derived1351 a h
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1208 := derived1208 a h
  have h8 : Entails.eval a c1277 := derived1277 a h
  have h9 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1362, some c1353, some c1351, some c1340, some c1363, some c1364, some c308, some c213, some c1208, some c1274, some c24, some c166, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1365 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 31) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c1362, c1353, c1351, c1340, c1363, c1364, c308, c213, c1208, c1274, c24, c166] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c1362 := derived1362 a h
  have h1 : Entails.eval a c1353 := derived1353 a h
  have h2 : Entails.eval a c1351 := derived1351 a h
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c1363 := derived1363 a h
  have h5 : Entails.eval a c1364 := derived1364 a h
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c1208 := derived1208 a h
  have h9 : Entails.eval a c1274 := derived1274 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1340, some c1351, some c1362, some c1365, some c1205, some c1234, some c1360, some c1330, some c1204, some c309, some c862, some c1208, some c256, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1366 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 31) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c1340, c1351, c1362, c1365, c1205, c1234, c1360, c1330, c1204, c309, c862, c1208, c256] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1351 := derived1351 a h
  have h2 : Entails.eval a c1362 := derived1362 a h
  have h3 : Entails.eval a c1365 := derived1365 a h
  have h4 : Entails.eval a c1205 := derived1205 a h
  have h5 : Entails.eval a c1234 := derived1234 a h
  have h6 : Entails.eval a c1360 := derived1360 a h
  have h7 : Entails.eval a c1330 := derived1330 a h
  have h8 : Entails.eval a c1204 := derived1204 a h
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c862 := h 861 (by decide)
  have h11 : Entails.eval a c1208 := derived1208 a h
  have h12 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1208, some c52, some c254, some c46, some c182, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1367 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 31) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c1366, c1208, c52, c254, c46, c182] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1208 := derived1208 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1205, some c1366, some c1330, some c1367, some c1162, some c1235, some c335, some c310, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1368 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 31) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c1205, c1366, c1330, c1367, c1162, c1235, c335, c310] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c1330 := derived1330 a h
  have h3 : Entails.eval a c1367 := derived1367 a h
  have h4 : Entails.eval a c1162 := derived1162 a h
  have h5 : Entails.eval a c1235 := derived1235 a h
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1368, some c1205, some c1366, some c1235, some c1260, some c29, some c5, some c1297, some c849, some c990, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1369 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 31) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c1368, c1205, c1366, c1235, c1260, c29, c5, c1297, c849, c990] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1235 := derived1235 a h
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1297 := derived1297 a h
  have h8 : Entails.eval a c849 := h 848 (by decide)
  have h9 : Entails.eval a c990 := derived990 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c223, some c1204, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1370 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 31) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c29, c223, c1204] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c223 := h 222 (by decide)
  have h2 : Entails.eval a c1204 := derived1204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1234, some c1368, some c1205, some c1366, some c1369, some c1370, some c1203, some c227, some c506, some c1249, some c61, some c137, some c732, some c728, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1371 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 31) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c1234, c1368, c1205, c1366, c1369, c1370, c1203, c227, c506, c1249, c61, c137, c732, c728] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c1234 := derived1234 a h
  have h1 : Entails.eval a c1368 := derived1368 a h
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c1369 := derived1369 a h
  have h5 : Entails.eval a c1370 := derived1370 a h
  have h6 : Entails.eval a c1203 := derived1203 a h
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c506 := h 505 (by decide)
  have h9 : Entails.eval a c1249 := derived1249 a h
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c732 := h 731 (by decide)
  have h13 : Entails.eval a c728 := h 727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1205, some c1234, some c1368, some c1371, some c1367, some c1332, some c35, some c313, some c1281, some c33, some c1321, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1372 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 31) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c1205, c1234, c1368, c1371, c1367, c1332, c35, c313, c1281, c33, c1321] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c1205 := derived1205 a h
  have h1 : Entails.eval a c1234 := derived1234 a h
  have h2 : Entails.eval a c1368 := derived1368 a h
  have h3 : Entails.eval a c1371 := derived1371 a h
  have h4 : Entails.eval a c1367 := derived1367 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c1321 := derived1321 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1372, some c1208, some c308, some c1367, some c35, some c50, some c1366, some c372, some c751, some c529, some c1241, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1373 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 31) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c1372, c1208, c308, c1367, c35, c50, c1366, c372, c751, c529, c1241] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c1372 := derived1372 a h
  have h1 : Entails.eval a c1208 := derived1208 a h
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c1367 := derived1367 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c1366 := derived1366 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c751 := h 750 (by decide)
  have h9 : Entails.eval a c529 := h 528 (by decide)
  have h10 : Entails.eval a c1241 := derived1241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨16, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c273, some c1251, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1374 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 31) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c29, c273, c1251] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1372, some c1366, some c1208, some c1367, some c308, some c1373, some c1235, some c520, some c33, some c253, some c1374, some c551, some c57, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1375 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 31) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1372, c1366, c1208, c1367, c308, c1373, c1235, c520, c33, c253, c1374, c551, c57] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1372 := derived1372 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c1208 := derived1208 a h
  have h3 : Entails.eval a c1367 := derived1367 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c1373 := derived1373 a h
  have h6 : Entails.eval a c1235 := derived1235 a h
  have h7 : Entails.eval a c520 := h 519 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c1374 := derived1374 a h
  have h11 : Entails.eval a c551 := h 550 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1372, some c1366, some c22, some c1135, some c399, some c26, some c85, some c192, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1376 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 31) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c1372, c1366, c22, c1135, c399, c26, c85, c192] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c1372 := derived1372 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1135 := derived1135 a h
  have h4 : Entails.eval a c399 := h 398 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1235, some c1375, some c1372, some c1376, some c335, some c5, some c310, some c273, some c1292, some c57, some c253, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1377 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 31) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c1366, c1235, c1375, c1372, c1376, c335, c5, c310, c273, c1292, c57, c253] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1375 := derived1375 a h
  have h3 : Entails.eval a c1372 := derived1372 a h
  have h4 : Entails.eval a c1376 := derived1376 a h
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c1292 := derived1292 a h
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c335, some c5, some c273, some c807, some c814, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1378 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 31) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c29, c335, c5, c273, c807, c814] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c807 := h 806 (by decide)
  have h5 : Entails.eval a c814 := h 813 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1375, some c1372, some c1366, some c1235, some c1377, some c1378, some c1255, some c22, some c1135, some c272, some c568, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1379 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 31) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1375, c1372, c1366, c1235, c1377, c1378, c1255, c22, c1135, c272, c568] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1235 := derived1235 a h
  have h4 : Entails.eval a c1377 := derived1377 a h
  have h5 : Entails.eval a c1378 := derived1378 a h
  have h6 : Entails.eval a c1255 := derived1255 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1135 := derived1135 a h
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c568 := h 567 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1375, some c1162, some c1372, some c1366, some c22, some c1135, some c1304, some c350, some c767, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1380 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 31) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c1375, c1162, c1372, c1366, c22, c1135, c1304, c350, c767] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1162 := derived1162 a h
  have h2 : Entails.eval a c1372 := derived1372 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1135 := derived1135 a h
  have h6 : Entails.eval a c1304 := derived1304 a h
  have h7 : Entails.eval a c350 := h 349 (by decide)
  have h8 : Entails.eval a c767 := h 766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c241, some c61, some c1249, some c1207, some c684, some c6, some c1283, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 31) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c241, c61, c1249, c1207, c684, c6, c1283] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c1249 := derived1249 a h
  have h3 : Entails.eval a c1207 := derived1207 a h
  have h4 : Entails.eval a c684 := h 683 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c1283 := derived1283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c815, some c1283, some c6, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1382 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 31) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c815, c1283, c6] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c815 := h 814 (by decide)
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1380, some c1375, some c252, some c1211, some c1140, some c171, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1383 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 31) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1380, c1375, c252, c1211, c1140, c171] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1380 := derived1380 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1375, some c1379, some c1162, some c1372, some c1366, some c1380, some c1381, some c1383, some c1316, some c1382, some c1241, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 31) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c1375, c1379, c1162, c1372, c1366, c1380, c1381, c1383, c1316, c1382, c1241] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1379 := derived1379 a h
  have h2 : Entails.eval a c1162 := derived1162 a h
  have h3 : Entails.eval a c1372 := derived1372 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c1380 := derived1380 a h
  have h6 : Entails.eval a c1381 := derived1381 a h
  have h7 : Entails.eval a c1383 := derived1383 a h
  have h8 : Entails.eval a c1316 := derived1316 a h
  have h9 : Entails.eval a c1382 := derived1382 a h
  have h10 : Entails.eval a c1241 := derived1241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1384, some c1375, some c1379, some c1162, some c1372, some c1366, some c592, some c252, some c1211, some c1140, some c886, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1385 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 31) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1384, c1375, c1379, c1162, c1372, c1366, c592, c252, c1211, c1140, c886] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1384 := derived1384 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1379 := derived1379 a h
  have h3 : Entails.eval a c1162 := derived1162 a h
  have h4 : Entails.eval a c1372 := derived1372 a h
  have h5 : Entails.eval a c1366 := derived1366 a h
  have h6 : Entails.eval a c592 := h 591 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c1211 := derived1211 a h
  have h9 : Entails.eval a c1140 := derived1140 a h
  have h10 : Entails.eval a c886 := h 885 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c684, some c86, some c588, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 31) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c684, c86, c588] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c684 := h 683 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c588 := h 587 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1379, some c1375, some c1385, some c61, some c1249, some c1386, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1387 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 31) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1379, c1375, c1385, c61, c1249, c1386] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  have h2 : Entails.eval a c1385 := derived1385 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c1249 := derived1249 a h
  have h5 : Entails.eval a c1386 := derived1386 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1375, some c1372, some c1366, some c1379, some c1162, some c1384, some c1387, some c22, some c1135, some c26, some c1247, some c192, some c138, some c781, some c56, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1388 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 31) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c1375, c1372, c1366, c1379, c1162, c1384, c1387, c22, c1135, c26, c1247, c192, c138, c781, c56] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c1375 := derived1375 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1379 := derived1379 a h
  have h4 : Entails.eval a c1162 := derived1162 a h
  have h5 : Entails.eval a c1384 := derived1384 a h
  have h6 : Entails.eval a c1387 := derived1387 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1135 := derived1135 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1247 := derived1247 a h
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c781 := h 780 (by decide)
  have h14 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1388, some c1372, some c1366, some c22, some c1135, some c62, some c26, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1389 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 31) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c1388, c1372, c1366, c22, c1135, c62, c26] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c1388 := derived1388 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1135 := derived1135 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1389, some c1372, some c1388, some c308, some c1375, some c241, some c1386, some c504, some c531, some c1213, some c507, some c338, some c877, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1390 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 31) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1389, c1372, c1388, c308, c1375, c241, c1386, c504, c531, c1213, c507, c338, c877] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1389 := derived1389 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c1388 := derived1388 a h
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c1375 := derived1375 a h
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c1386 := derived1386 a h
  have h7 : Entails.eval a c504 := h 503 (by decide)
  have h8 : Entails.eval a c531 := h 530 (by decide)
  have h9 : Entails.eval a c1213 := derived1213 a h
  have h10 : Entails.eval a c507 := h 506 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c877 := h 876 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1390, some c1389, some c1388, some c68, some c1372, some c308, some c1375, some c1366, some c619, some c1382, some c338, some c310, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1391 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 31) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c1390, c1389, c1388, c68, c1372, c308, c1375, c1366, c619, c1382, c338, c310] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c1390 := derived1390 a h
  have h1 : Entails.eval a c1389 := derived1389 a h
  have h2 : Entails.eval a c1388 := derived1388 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c1372 := derived1372 a h
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c1375 := derived1375 a h
  have h7 : Entails.eval a c1366 := derived1366 a h
  have h8 : Entails.eval a c619 := h 618 (by decide)
  have h9 : Entails.eval a c1382 := derived1382 a h
  have h10 : Entails.eval a c338 := h 337 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1390, some c1389, some c1388, some c68, some c1372, some c308, some c1375, some c1366, some c687, some c1383, some c813, some c1206, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1392 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 31) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c1390, c1389, c1388, c68, c1372, c308, c1375, c1366, c687, c1383, c813, c1206] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c1390 := derived1390 a h
  have h1 : Entails.eval a c1389 := derived1389 a h
  have h2 : Entails.eval a c1388 := derived1388 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c1372 := derived1372 a h
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c1375 := derived1375 a h
  have h7 : Entails.eval a c1366 := derived1366 a h
  have h8 : Entails.eval a c687 := h 686 (by decide)
  have h9 : Entails.eval a c1383 := derived1383 a h
  have h10 : Entails.eval a c813 := h 812 (by decide)
  have h11 : Entails.eval a c1206 := derived1206 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1372, some c1375, some c1388, some c308, some c68, some c1389, some c1390, some c1392, some c619, some c1391, some c1378, some c1241, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1393 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 31) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c1366, c1372, c1375, c1388, c308, c68, c1389, c1390, c1392, c619, c1391, c1378, c1241] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1372 := derived1372 a h
  have h2 : Entails.eval a c1375 := derived1375 a h
  have h3 : Entails.eval a c1388 := derived1388 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c1389 := derived1389 a h
  have h7 : Entails.eval a c1390 := derived1390 a h
  have h8 : Entails.eval a c1392 := derived1392 a h
  have h9 : Entails.eval a c619 := h 618 (by decide)
  have h10 : Entails.eval a c1391 := derived1391 a h
  have h11 : Entails.eval a c1378 := derived1378 a h
  have h12 : Entails.eval a c1241 := derived1241 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1394 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c193, some c619, some c5, some c11, some c32, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1394 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 31) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c1366, c193, c619, c5, c11, c32] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c619 := h 618 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c193, some c1393, some c1394, some c312, some c1295, some c661, some c29, some c222, some c11, some c480, some c822, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1395 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 31) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c1366, c193, c1393, c1394, c312, c1295, c661, c29, c222, c11, c480, c822] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1394 := derived1394 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c1295 := derived1295 a h
  have h6 : Entails.eval a c661 := h 660 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c222 := h 221 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c480 := h 479 (by decide)
  have h11 : Entails.eval a c822 := h 821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c352, some c698, some c30, some c1323, some c1301, some c69, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 31) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c352, c698, c30, c1323, c1301, c69] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c698 := h 697 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1323 := derived1323 a h
  have h4 : Entails.eval a c1301 := derived1301 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c193, some c1393, some c1395, some c697, some c252, some c1396, some c312, some c635, some c1206, some c814, some c638, some c120, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 31) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1366, c193, c1393, c1395, c697, c252, c1396, c312, c635, c1206, c814, c638, c120] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1395 := derived1395 a h
  have h4 : Entails.eval a c697 := h 696 (by decide)
  have h5 : Entails.eval a c252 := h 251 (by decide)
  have h6 : Entails.eval a c1396 := derived1396 a h
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c635 := h 634 (by decide)
  have h9 : Entails.eval a c1206 := derived1206 a h
  have h10 : Entails.eval a c814 := h 813 (by decide)
  have h11 : Entails.eval a c638 := h 637 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1397, some c1208, some c46, some c312, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 31) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c1397, c1208, c46, c312] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c1397 := derived1397 a h
  have h1 : Entails.eval a c1208 := derived1208 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1208, some c1367, some c46, some c50, some c257, some c157, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 31) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c1208, c1367, c46, c50, c257, c157] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c1208 := derived1208 a h
  have h1 : Entails.eval a c1367 := derived1367 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c257, some c157, some c52, some c1399, some c1366, some c193, some c252, some c286, some c122, some c1163, some c1162, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 31) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1398, c257, c157, c52, c1399, c1366, c193, c252, c286, c122, c1163, c1162] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c1399 := derived1399 a h
  have h5 : Entails.eval a c1366 := derived1366 a h
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c1163 := derived1163 a h
  have h11 : Entails.eval a c1162 := derived1162 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c1366, some c193, some c1393, some c257, some c52, some c157, some c1400, some c1098, some c29, some c765, some c1243, some c1289, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 31) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1398, c1366, c193, c1393, c257, c52, c157, c1400, c1098, c29, c765, c1243, c1289] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c1400 := derived1400 a h
  have h8 : Entails.eval a c1098 := derived1098 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c765 := h 764 (by decide)
  have h11 : Entails.eval a c1243 := derived1243 a h
  have h12 : Entails.eval a c1289 := derived1289 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c1399, some c1366, some c193, some c1393, some c637, some c661, some c587, some c30, some c1295, some c912, some c232, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 31) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1398, c1399, c1366, c193, c1393, c637, c661, c587, c30, c1295, c912, c232] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1399 := derived1399 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c1393 := derived1393 a h
  have h5 : Entails.eval a c637 := h 636 (by decide)
  have h6 : Entails.eval a c661 := h 660 (by decide)
  have h7 : Entails.eval a c587 := h 586 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c1295 := derived1295 a h
  have h10 : Entails.eval a c912 := h 911 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c17, some c1222, some c284, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 31) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c252, c17, c1222, c284] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c1222 := derived1222 a h
  have h3 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c1399, some c1393, some c1401, some c1402, some c139, some c1403, some c1295, some c957, some c601, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 31) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c1398, c1399, c1393, c1401, c1402, c139, c1403, c1295, c957, c601] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1399 := derived1399 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1401 := derived1401 a h
  have h4 : Entails.eval a c1402 := derived1402 a h
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c1403 := derived1403 a h
  have h7 : Entails.eval a c1295 := derived1295 a h
  have h8 : Entails.eval a c957 := derived957 a h
  have h9 : Entails.eval a c601 := h 600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1404, some c1398, some c1399, some c1393, some c1366, some c1402, some c139, some c1403, some c1382, some c1295, some c694, some c730, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 31) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1404, c1398, c1399, c1393, c1366, c1402, c139, c1403, c1382, c1295, c694, c730] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1404 := derived1404 a h
  have h1 : Entails.eval a c1398 := derived1398 a h
  have h2 : Entails.eval a c1399 := derived1399 a h
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c1402 := derived1402 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c1403 := derived1403 a h
  have h8 : Entails.eval a c1382 := derived1382 a h
  have h9 : Entails.eval a c1295 := derived1295 a h
  have h10 : Entails.eval a c694 := h 693 (by decide)
  have h11 : Entails.eval a c730 := h 729 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1405, some c1404, some c1398, some c1399, some c1366, some c193, some c1393, some c1382, some c1098, some c1289, some c1305, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 31) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c1405, c1404, c1398, c1399, c1366, c193, c1393, c1382, c1098, c1289, c1305] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1404 := derived1404 a h
  have h2 : Entails.eval a c1398 := derived1398 a h
  have h3 : Entails.eval a c1399 := derived1399 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c1393 := derived1393 a h
  have h7 : Entails.eval a c1382 := derived1382 a h
  have h8 : Entails.eval a c1098 := derived1098 a h
  have h9 : Entails.eval a c1289 := derived1289 a h
  have h10 : Entails.eval a c1305 := derived1305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c1399, some c1406, some c252, some c1404, some c17, some c171, some c284, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 31) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c1398, c1399, c1406, c252, c1404, c17, c171, c284] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1399 := derived1399 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c1404 := derived1404 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1404, some c1405, some c1406, some c1407, some c179, some c1224, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 31) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1404, c1405, c1406, c1407, c179, c1224] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1404 := derived1404 a h
  have h1 : Entails.eval a c1405 := derived1405 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1407 := derived1407 a h
  have h4 : Entails.eval a c179 := h 178 (by decide)
  have h5 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1208, some c1393, some c1221, some c179, some c1286, some c176, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1409 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 31) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c1208, c1393, c1221, c179, c1286, c176] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c1208 := derived1208 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c1286 := derived1286 a h
  have h5 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1208, some c1408, some c1366, some c252, some c1409, some c732, some c171, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1410 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 31) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c1208, c1408, c1366, c252, c1409, c732, c171] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c1208 := derived1208 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c1409 := derived1409 a h
  have h5 : Entails.eval a c732 := h 731 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1249, some c683, some c191, some c137, some c84, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1411 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 31) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c1249, c683, c191, c137, c84] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c1249 := derived1249 a h
  have h1 : Entails.eval a c683 := h 682 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1408, some c1393, some c1366, some c1208, some c1410, some c1411, some c1221, some c14, some c1305, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1412 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 31) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1408, c1393, c1366, c1208, c1410, c1411, c1221, c14, c1305] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1408 := derived1408 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1208 := derived1208 a h
  have h4 : Entails.eval a c1410 := derived1410 a h
  have h5 : Entails.eval a c1411 := derived1411 a h
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c1305 := derived1305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1393, some c1366, some c254, some c54, some c14, some c1230, some c310, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1413 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 31) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c1393, c1366, c254, c54, c14, c1230, c310] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c1393 := derived1393 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c254 := h 253 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c1230 := derived1230 a h
  have h6 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1412, some c1408, some c1413, some c253, some c76, some c1369, some c16, some c1370, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1414 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 31) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c1412, c1408, c1413, c253, c76, c1369, c16, c1370] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c1413 := derived1413 a h
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c1369 := derived1369 a h
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c1370 := derived1370 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1414, some c252, some c1412, some c1408, some c1393, some c253, some c76, some c1368, some c686, some c94, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1415 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 31) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c1414, c252, c1412, c1408, c1393, c253, c76, c1368, c686, c94] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c1414 := derived1414 a h
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1408 := derived1408 a h
  have h4 : Entails.eval a c1393 := derived1393 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c1368 := derived1368 a h
  have h8 : Entails.eval a c686 := h 685 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1412, some c1408, some c1393, some c1366, some c1415, some c254, some c1286, some c872, some c682, some c502, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1416 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 31) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1412, c1408, c1393, c1366, c1415, c254, c1286, c872, c682, c502] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c1415 := derived1415 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c1286 := derived1286 a h
  have h7 : Entails.eval a c872 := h 871 (by decide)
  have h8 : Entails.eval a c682 := h 681 (by decide)
  have h9 : Entails.eval a c502 := h 501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1416

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
