import MerLeanExperiment.Certificates.B16_8_2.Steps0800_0899

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1281 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨43, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1281 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1248, some c169, some c172, some c374, some c379, some c373, some c359, some c71, some c1280, some c1277, some c48, some c49, some c288, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1281 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1281 : lratChecker f1281 p1281 = .success := by decide +kernel
theorem unsat1281 : Unsatisfiable (PosFin 57) f1281 := by
  apply lratCheckerSound f1281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1281
  · intro a ha; simp [p1281] at ha; subst a; trivial
  · exact checked1281
theorem derived1281 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1281 := by
  apply localUnsat_implies_entails f1281 [c1251, c1248, c169, c172, c374, c379, c373, c359, c71, c1280, c1277, c48, c49, c288] c1281 unsat1281 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1248 := derived1248 a h
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c1280 := derived1280 a h
  have h10 : Entails.eval a c1277 := derived1277 a h
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1282 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1282 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1251, some c5, some c10, some c1245, some c1279, some c1281, some c358, some c379, some c376, some c172, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1282 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1282 : lratChecker f1282 p1282 = .success := by decide +kernel
theorem unsat1282 : Unsatisfiable (PosFin 57) f1282 := by
  apply lratCheckerSound f1282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1282
  · intro a ha; simp [p1282] at ha; subst a; trivial
  · exact checked1282
theorem derived1282 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1282 := by
  apply localUnsat_implies_entails f1282 [c100, c1251, c5, c10, c1245, c1279, c1281, c358, c379, c376, c172] c1282 unsat1282 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1245 := derived1245 a h
  have h5 : Entails.eval a c1279 := derived1279 a h
  have h6 : Entails.eval a c1281 := derived1281 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1283 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨13, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1283 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c1281, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1283 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1283 : lratChecker f1283 p1283 = .success := by decide +kernel
theorem unsat1283 : Unsatisfiable (PosFin 57) f1283 := by
  apply lratCheckerSound f1283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1283
  · intro a ha; simp [p1283] at ha; subst a; trivial
  · exact checked1283
theorem derived1283 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1283 := by
  apply localUnsat_implies_entails f1283 [c1245, c1281] c1283 unsat1283 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1284 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1284 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1283, some c7, some c1269, some c1273, some c72, some c841, some c374, some c71, some c170, some c149, some c379, some c365, some c153, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1284 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1284 : lratChecker f1284 p1284 = .success := by decide +kernel
theorem unsat1284 : Unsatisfiable (PosFin 57) f1284 := by
  apply lratCheckerSound f1284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1284
  · intro a ha; simp [p1284] at ha; subst a; trivial
  · exact checked1284
theorem derived1284 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1284 := by
  apply localUnsat_implies_entails f1284 [c1251, c1283, c7, c1269, c1273, c72, c841, c374, c71, c170, c149, c379, c365, c153] c1284 unsat1284 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c1273 := derived1273 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1285 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1285 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1284, some c1274, some c7, some c1245, some c151, some c379, some c376, some c172, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1285 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1285 : lratChecker f1285 p1285 = .success := by decide +kernel
theorem unsat1285 : Unsatisfiable (PosFin 57) f1285 := by
  apply lratCheckerSound f1285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1285
  · intro a ha; simp [p1285] at ha; subst a; trivial
  · exact checked1285
theorem derived1285 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1285 := by
  apply localUnsat_implies_entails f1285 [c1251, c1284, c1274, c7, c1245, c151, c379, c376, c172] c1285 unsat1285 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1284 := derived1284 a h
  have h2 : Entails.eval a c1274 := derived1274 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1245 := derived1245 a h
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1286 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1286 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c1251, some c379, some c1118, some c499, some c374, some c72, some c1280, some c1277, some c48, some c49, some c288, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1286 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1286 : lratChecker f1286 p1286 = .success := by decide +kernel
theorem unsat1286 : Unsatisfiable (PosFin 57) f1286 := by
  apply lratCheckerSound f1286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1286
  · intro a ha; simp [p1286] at ha; subst a; trivial
  · exact checked1286
theorem derived1286 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1286 := by
  apply localUnsat_implies_entails f1286 [c97, c1251, c379, c1118, c499, c374, c72, c1280, c1277, c48, c49, c288] c1286 unsat1286 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c499 := derived499 a h
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c1280 := derived1280 a h
  have h8 : Entails.eval a c1277 := derived1277 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1287 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1287 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c368, some c356, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1287 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1287 : lratChecker f1287 p1287 = .success := by decide +kernel
theorem unsat1287 : Unsatisfiable (PosFin 57) f1287 := by
  apply lratCheckerSound f1287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1287
  · intro a ha; simp [p1287] at ha; subst a; trivial
  · exact checked1287
theorem derived1287 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1287 := by
  apply localUnsat_implies_entails f1287 [c371, c368, c356] c1287 unsat1287 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1288 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1288 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c366, some c356, some c72, some c365, some c841, some c71, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1288 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1288 : lratChecker f1288 p1288 = .success := by decide +kernel
theorem unsat1288 : Unsatisfiable (PosFin 57) f1288 := by
  apply lratCheckerSound f1288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1288
  · intro a ha; simp [p1288] at ha; subst a; trivial
  · exact checked1288
theorem derived1288 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1288 := by
  apply localUnsat_implies_entails f1288 [c369, c366, c356, c72, c365, c841, c71] c1288 unsat1288 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1289 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨34, by decide⟩, true), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c278, some c297, some c190, some c23, some c21, some c202, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 57) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c301, c278, c297, c190, c23, c21, c202] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c297 := h 296 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c98, some c1278, some c1282, some c1285, some c1251, some c1248, some c1286, some c1287, some c151, some c158, some c1288, some c162, some c7, some c169, some c150, some c374, some c72, some c1256, some c367, some c71, some c1289, some c48, some c49, some c36, some c299, some c280, some c337, some c190, some c191, some c21, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 57) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c100, c97, c98, c1278, c1282, c1285, c1251, c1248, c1286, c1287, c151, c158, c1288, c162, c7, c169, c150, c374, c72, c1256, c367, c71, c1289, c48, c49, c36, c299, c280, c337, c190, c191, c21] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1278 := derived1278 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1285 := derived1285 a h
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c1248 := derived1248 a h
  have h8 : Entails.eval a c1286 := derived1286 a h
  have h9 : Entails.eval a c1287 := derived1287 a h
  have h10 : Entails.eval a c151 := h 150 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c1288 := derived1288 a h
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c72 := h 71 (by decide)
  have h19 : Entails.eval a c1256 := derived1256 a h
  have h20 : Entails.eval a c367 := h 366 (by decide)
  have h21 : Entails.eval a c71 := h 70 (by decide)
  have h22 : Entails.eval a c1289 := derived1289 a h
  have h23 : Entails.eval a c48 := h 47 (by decide)
  have h24 : Entails.eval a c49 := h 48 (by decide)
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c299 := h 298 (by decide)
  have h27 : Entails.eval a c280 := h 279 (by decide)
  have h28 : Entails.eval a c337 := h 336 (by decide)
  have h29 : Entails.eval a c190 := h 189 (by decide)
  have h30 : Entails.eval a c191 := h 190 (by decide)
  have h31 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c174, some c379, some c376, some c1287, some c1288, some c158, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 57) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c154, c174, c379, c376, c1287, c1288, c158] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c1288 := derived1288 a h
  have h6 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c98, some c1291, some c379, some c151, some c1118, some c499, some c368, some c373, some c150, some c157, some c367, some c72, some c1233, some c1242, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 57) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c97, c98, c1291, c379, c151, c1118, c499, c368, c373, c150, c157, c367, c72, c1233, c1242] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1291 := derived1291 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c499 := derived499 a h
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c1233 := derived1233 a h
  have h14 : Entails.eval a c1242 := derived1242 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨34, by decide⟩, true), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c278, some c297, some c284, some c190, some c1255, some c228, some c21, some c276, some c203, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c278, c297, c284, c190, c1255, c228, c21, c276, c203] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c278 := h 277 (by decide)
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c1255 := derived1255 a h
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1251, some c362, some c371, some c151, some c158, some c376, some c365, some c169, some c150, some c71, some c1039, some c72, some c1256, some c1293, some c48, some c49, some c36, some c299, some c280, some c337, some c190, some c191, some c21, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1294 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 57) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c100, c1251, c362, c371, c151, c158, c376, c365, c169, c150, c71, c1039, c72, c1256, c1293, c48, c49, c36, c299, c280, c337, c190, c191, c21] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c1039 := derived1039 a h
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c1256 := derived1256 a h
  have h14 : Entails.eval a c1293 := derived1293 a h
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c337 := h 336 (by decide)
  have h21 : Entails.eval a c190 := h 189 (by decide)
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1278, some c100, some c97, some c98, some c1251, some c1282, some c1285, some c1290, some c1291, some c7, some c1292, some c1294, some c369, some c150, some c157, some c376, some c366, some c151, some c1118, some c499, some c72, some c841, some c1242, some c1233, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1295 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 57) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c1278, c100, c97, c98, c1251, c1282, c1285, c1290, c1291, c7, c1292, c1294, c369, c150, c157, c376, c366, c151, c1118, c499, c72, c841, c1242, c1233] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c1278 := derived1278 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1251 := derived1251 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1285 := derived1285 a h
  have h7 : Entails.eval a c1290 := derived1290 a h
  have h8 : Entails.eval a c1291 := derived1291 a h
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c1292 := derived1292 a h
  have h11 : Entails.eval a c1294 := derived1294 a h
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c499 := derived499 a h
  have h20 : Entails.eval a c72 := h 71 (by decide)
  have h21 : Entails.eval a c841 := derived841 a h
  have h22 : Entails.eval a c1242 := derived1242 a h
  have h23 : Entails.eval a c1233 := derived1233 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c10, some c141, some c125, some c191, some c26, some c21, some c108, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1296 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 57) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c5, c10, c141, c125, c191, c26, c21, c108] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c300, some c1277, some c340, some c174, some c129, some c145, some c270, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1297 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 57) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c379, c300, c1277, c340, c174, c129, c145, c270] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c100, some c98, some c1251, some c1278, some c1295, some c80, some c734, some c1253, some c1266, some c159, some c1296, some c158, some c372, some c1297, some c153, some c128, some c144, some c193, some c17, some c26, some c106, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1298 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 57) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c97, c100, c98, c1251, c1278, c1295, c80, c734, c1253, c1266, c159, c1296, c158, c372, c1297, c153, c128, c144, c193, c17, c26, c106] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1251 := derived1251 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c1295 := derived1295 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c734 := derived734 a h
  have h8 : Entails.eval a c1253 := derived1253 a h
  have h9 : Entails.eval a c1266 := derived1266 a h
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c1296 := derived1296 a h
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c1297 := derived1297 a h
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨47, by decide⟩, false), (⟨46, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1245, some c1257, some c1262, some c72, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1299 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 57) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c1251, c1245, c1257, c1262, c72] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1245 := derived1245 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c1262 := derived1262 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1280, some c1277, some c48, some c49, some c288, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 57) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c1251, c1280, c1277, c48, c49, c288] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1280 := derived1280 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1245, some c1248, some c150, some c172, some c369, some c379, some c84, some c1299, some c182, some c1300, some c72, some c167, some c374, some c365, some c354, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1301 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 57) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c1251, c1245, c1248, c150, c172, c369, c379, c84, c1299, c182, c1300, c72, c167, c374, c365, c354] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1245 := derived1245 a h
  have h2 : Entails.eval a c1248 := derived1248 a h
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c1299 := derived1299 a h
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c1300 := derived1300 a h
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c5, some c1245, some c100, some c1251, some c1282, some c1301, some c96, some c70, some c841, some c369, some c72, some c150, some c366, some c1247, some c376, some c354, some c1261, some c373, some c182, some c179, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1302 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 57) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c10, c5, c1245, c100, c1251, c1282, c1301, c96, c70, c841, c369, c72, c150, c366, c1247, c376, c354, c1261, c373, c182, c179] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c1245 := derived1245 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1251 := derived1251 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1301 := derived1301 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c1247 := derived1247 a h
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c1261 := derived1261 a h
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c182 := h 181 (by decide)
  have h20 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨15, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c1277, some c38, some c52, some c60, some c330, some c119, some c127, some c143, some c262, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 57) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c301, c1277, c38, c52, c60, c330, c119, c127, c143, c262] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨43, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c377, some c365, some c354, some c374, some c373, some c1119, some c173, some c1303, some c48, some c36, some c288, some c286, some c341, some c340, some c271, some c64, some c328, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1304 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 57) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c379, c377, c365, c354, c374, c373, c1119, c173, c1303, c48, c36, c288, c286, c341, c340, c271, c64, c328] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c1119 := derived1119 a h
  have h7 : Entails.eval a c173 := h 172 (by decide)
  have h8 : Entails.eval a c1303 := derived1303 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c288 := h 287 (by decide)
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c340 := h 339 (by decide)
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c64 := h 63 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c377, some c150, some c172, some c369, some c379, some c84, some c1304, some c167, some c367, some c354, some c373, some c173, some c1303, some c48, some c36, some c288, some c127, some c341, some c64, some c328, some c143, some c267, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1305 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 57) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1245, c377, c150, c172, c369, c379, c84, c1304, c167, c367, c354, c373, c173, c1303, c48, c36, c288, c127, c341, c64, c328, c143, c267] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1304 := derived1304 a h
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c373 := h 372 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c1303 := derived1303 a h
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c143 := h 142 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c1245, some c1305, some c931, some c70, some c841, some c1119, some c179, some c366, some c379, some c373, some c354, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1306 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 57) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c4, c1245, c1305, c931, c70, c841, c1119, c179, c366, c379, c373, c354] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c1245 := derived1245 a h
  have h2 : Entails.eval a c1305 := derived1305 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c1119 := derived1119 a h
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c373 := h 372 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c4, some c1306, some c92, some c841, some c1119, some c179, some c380, some c373, some c354, some c366, some c367, some c84, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1307 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 57) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1245, c4, c1306, c92, c841, c1119, c179, c380, c373, c354, c366, c367, c84] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c1306 := derived1306 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c1119 := derived1119 a h
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c1277, some c52, some c60, some c288, some c328, some c196, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1308 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 57) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c301, c1277, c52, c60, c288, c328, c196] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1308, some c48, some c36, some c288, some c341, some c196, some c64, some c328, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1309 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 57) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c1308, c48, c36, c288, c341, c196, c64, c328] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c1308 := derived1308 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨43, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c377, some c169, some c374, some c373, some c359, some c71, some c1309, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1310 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 57) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c379, c377, c169, c374, c373, c359, c71, c1309] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c374 := h 373 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c1309 := derived1309 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1311 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨43, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1311 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c1310, some c931, some c70, some c841, some c373, some c359, some c149, some c366, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1311 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1311 : lratChecker f1311 p1311 = .success := by decide +kernel
theorem unsat1311 : Unsatisfiable (PosFin 57) f1311 := by
  apply lratCheckerSound f1311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1311
  · intro a ha; simp [p1311] at ha; subst a; trivial
  · exact checked1311
theorem derived1311 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1311 := by
  apply localUnsat_implies_entails f1311 [c379, c1310, c931, c70, c841, c373, c359, c149, c366] c1311 unsat1311 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c1310 := derived1310 a h
  have h2 : Entails.eval a c931 := derived931 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1312 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1312 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c1311, some c172, some c377, some c376, some c931, some c70, some c841, some c369, some c359, some c157, some c366, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1312 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1312 : lratChecker f1312 p1312 = .success := by decide +kernel
theorem unsat1312 : Unsatisfiable (PosFin 57) f1312 := by
  apply lratCheckerSound f1312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1312
  · intro a ha; simp [p1312] at ha; subst a; trivial
  · exact checked1312
theorem derived1312 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1312 := by
  apply localUnsat_implies_entails f1312 [c1245, c1311, c172, c377, c376, c931, c70, c841, c369, c359, c157, c366] c1312 unsat1312 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c1311 := derived1311 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1313 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨9, by decide⟩, true), (⟨43, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1313 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c380, some c373, some c359, some c149, some c366, some c367, some c84, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1313 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1313 : lratChecker f1313 p1313 = .success := by decide +kernel
theorem unsat1313 : Unsatisfiable (PosFin 57) f1313 := by
  apply lratCheckerSound f1313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1313
  · intro a ha; simp [p1313] at ha; subst a; trivial
  · exact checked1313
theorem derived1313 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1313 := by
  apply localUnsat_implies_entails f1313 [c841, c380, c373, c359, c149, c366, c367, c84] c1313 unsat1313 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1314 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1314 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c278, some c318, some c324, some c264, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1314 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1314 : lratChecker f1314 p1314 = .success := by decide +kernel
theorem unsat1314 : Unsatisfiable (PosFin 57) f1314 := by
  apply lratCheckerSound f1314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1314
  · intro a ha; simp [p1314] at ha; subst a; trivial
  · exact checked1314
theorem derived1314 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1314 := by
  apply localUnsat_implies_entails f1314 [c284, c278, c318, c324, c264] c1314 unsat1314 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1315 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1315 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c328, some c326, some c217, some c219, some c232, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1315 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1315 : lratChecker f1315 p1315 = .success := by decide +kernel
theorem unsat1315 : Unsatisfiable (PosFin 57) f1315 := by
  apply lratCheckerSound f1315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1315
  · intro a ha; simp [p1315] at ha; subst a; trivial
  · exact checked1315
theorem derived1315 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1315 := by
  apply localUnsat_implies_entails f1315 [c60, c328, c326, c217, c219, c232] c1315 unsat1315 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c217 := h 216 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1316 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1316 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c157, some c1315, some c1314, some c48, some c288, some c286, some c205, some c207, some c232, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1316 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1316 : lratChecker f1316 p1316 = .success := by decide +kernel
theorem unsat1316 : Unsatisfiable (PosFin 57) f1316 := by
  apply lratCheckerSound f1316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1316
  · intro a ha; simp [p1316] at ha; subst a; trivial
  · exact checked1316
theorem derived1316 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1316 := by
  apply localUnsat_implies_entails f1316 [c367, c157, c1315, c1314, c48, c288, c286, c205, c207, c232] c1316 unsat1316 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c1315 := derived1315 a h
  have h3 : Entails.eval a c1314 := derived1314 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1317 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1317 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1316, some c84, some c369, some c366, some c157, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1317 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1317 : lratChecker f1317 p1317 = .success := by decide +kernel
theorem unsat1317 : Unsatisfiable (PosFin 57) f1317 := by
  apply lratCheckerSound f1317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1317
  · intro a ha; simp [p1317] at ha; subst a; trivial
  · exact checked1317
theorem derived1317 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1317 := by
  apply localUnsat_implies_entails f1317 [c1316, c84, c369, c366, c157] c1317 unsat1317 (by rfl) a
  have h0 : Entails.eval a c1316 := derived1316 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1318 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1318 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c5, some c26, some c21, some c108, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1318 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1318 : lratChecker f1318 p1318 = .success := by decide +kernel
theorem unsat1318 : Unsatisfiable (PosFin 57) f1318 := by
  apply lratCheckerSound f1318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1318
  · intro a ha; simp [p1318] at ha; subst a; trivial
  · exact checked1318
theorem derived1318 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1318 := by
  apply localUnsat_implies_entails f1318 [c10, c5, c26, c21, c108] c1318 unsat1318 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1319 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨16, by decide⟩, false), (⟨55, by decide⟩, false), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c946, some c84, some c339, some c369, some c215, some c161, some c148, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c946, c84, c339, c369, c215, c161, c148] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨47, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c284, some c1314, some c60, some c326, some c339, some c331, some c193, some c210, some c17, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c97, c284, c1314, c60, c326, c339, c331, c193, c210, c17] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c1314 := derived1314 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1298, some c97, some c100, some c5, some c10, some c1245, some c1302, some c1307, some c1088, some c1312, some c92, some c841, some c1313, some c153, some c179, some c1317, some c359, some c1318, some c1319, some c365, some c149, some c157, some c1320, some c48, some c36, some c291, some c299, some c286, some c324, some c198, some c193, some c17, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c1298, c97, c100, c5, c10, c1245, c1302, c1307, c1088, c1312, c92, c841, c1313, c153, c179, c1317, c359, c1318, c1319, c365, c149, c157, c1320, c48, c36, c291, c299, c286, c324, c198, c193, c17] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c1298 := derived1298 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c1245 := derived1245 a h
  have h6 : Entails.eval a c1302 := derived1302 a h
  have h7 : Entails.eval a c1307 := derived1307 a h
  have h8 : Entails.eval a c1088 := derived1088 a h
  have h9 : Entails.eval a c1312 := derived1312 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c1313 := derived1313 a h
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c179 := h 178 (by decide)
  have h15 : Entails.eval a c1317 := derived1317 a h
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c1318 := derived1318 a h
  have h18 : Entails.eval a c1319 := derived1319 a h
  have h19 : Entails.eval a c365 := h 364 (by decide)
  have h20 : Entails.eval a c149 := h 148 (by decide)
  have h21 : Entails.eval a c157 := h 156 (by decide)
  have h22 : Entails.eval a c1320 := derived1320 a h
  have h23 : Entails.eval a c48 := h 47 (by decide)
  have h24 : Entails.eval a c36 := h 35 (by decide)
  have h25 : Entails.eval a c291 := h 290 (by decide)
  have h26 : Entails.eval a c299 := h 298 (by decide)
  have h27 : Entails.eval a c286 := h 285 (by decide)
  have h28 : Entails.eval a c324 := h 323 (by decide)
  have h29 : Entails.eval a c198 := h 197 (by decide)
  have h30 : Entails.eval a c193 := h 192 (by decide)
  have h31 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c151, some c379, some c376, some c172, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c1245, c151, c379, c376, c172] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c379, some c1118, some c1138, some c175, some c1300, some c841, some c96, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c1251, c379, c1118, c1138, c175, c1300, c841, c96] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c1138 := derived1138 a h
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c1300 := derived1300 a h
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1275, some c182, some c1323, some c153, some c179, some c371, some c841, some c151, some c163, some c71, some c96, some c376, some c367, some c1280, some c374, some c341, some c353, some c38, some c1314, some c303, some c49, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1251, c1275, c182, c1323, c153, c179, c371, c841, c151, c163, c71, c96, c376, c367, c1280, c374, c341, c353, c38, c1314, c303, c49] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1275 := derived1275 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c1323 := derived1323 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c1280 := derived1280 a h
  have h15 : Entails.eval a c374 := h 373 (by decide)
  have h16 : Entails.eval a c341 := h 340 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c1314 := derived1314 a h
  have h20 : Entails.eval a c303 := h 302 (by decide)
  have h21 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c380, some c92, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c379, c380, c92] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c1118, some c1138, some c175, some c368, some c367, some c841, some c92, some c96, some c377, some c374, some c353, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c151, c1118, c1138, c175, c368, c367, c841, c92, c96, c377, c374, c353] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c1138 := derived1138 a h
  have h3 : Entails.eval a c175 := h 174 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨14, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c278, some c38, some c190, some c139, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c301, c278, c38, c190, c139] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1321, some c1298, some c97, some c100, some c1324, some c4, some c1326, some c1325, some c153, some c179, some c371, some c841, some c163, some c71, some c92, some c96, some c367, some c1322, some c376, some c374, some c1031, some c353, some c369, some c1269, some c1327, some c48, some c36, some c288, some c286, some c341, some c324, some c271, some c64, some c328, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c1321, c1298, c97, c100, c1324, c4, c1326, c1325, c153, c179, c371, c841, c163, c71, c92, c96, c367, c1322, c376, c374, c1031, c353, c369, c1269, c1327, c48, c36, c288, c286, c341, c324, c271, c64, c328] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c1321 := derived1321 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c1326 := derived1326 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  have h17 : Entails.eval a c1322 := derived1322 a h
  have h18 : Entails.eval a c376 := h 375 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c1031 := derived1031 a h
  have h21 : Entails.eval a c353 := h 352 (by decide)
  have h22 : Entails.eval a c369 := h 368 (by decide)
  have h23 : Entails.eval a c1269 := derived1269 a h
  have h24 : Entails.eval a c1327 := derived1327 a h
  have h25 : Entails.eval a c48 := h 47 (by decide)
  have h26 : Entails.eval a c36 := h 35 (by decide)
  have h27 : Entails.eval a c288 := h 287 (by decide)
  have h28 : Entails.eval a c286 := h 285 (by decide)
  have h29 : Entails.eval a c341 := h 340 (by decide)
  have h30 : Entails.eval a c324 := h 323 (by decide)
  have h31 : Entails.eval a c271 := h 270 (by decide)
  have h32 : Entails.eval a c64 := h 63 (by decide)
  have h33 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1325, some c1118, some c170, some c373, some c96, some c1300, some c374, some c72, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c1325, c1118, c170, c373, c96, c1300, c374, c72] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c1325 := derived1325 a h
  have h1 : Entails.eval a c1118 := derived1118 a h
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c1300 := derived1300 a h
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1329, some c153, some c371, some c151, some c158, some c376, some c1288, some c365, some c84, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c1251, c1329, c153, c371, c151, c158, c376, c1288, c365, c84] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1329 := derived1329 a h
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c1288 := derived1288 a h
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1330, some c1325, some c151, some c170, some c1245, some c373, some c8, some c96, some c175, some c374, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c1330, c1325, c151, c170, c1245, c373, c8, c96, c175, c374] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c1330 := derived1330 a h
  have h1 : Entails.eval a c1325 := derived1325 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c1245 := derived1245 a h
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1321, some c1298, some c97, some c100, some c1328, some c1330, some c1331, some c153, some c371, some c151, some c158, some c365, some c71, some c841, some c179, some c8, some c1088, some c1319, some c26, some c21, some c108, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c1321, c1298, c97, c100, c1328, c1330, c1331, c153, c371, c151, c158, c365, c71, c841, c179, c8, c1088, c1319, c26, c21, c108] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c1321 := derived1321 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1328 := derived1328 a h
  have h5 : Entails.eval a c1330 := derived1330 a h
  have h6 : Entails.eval a c1331 := derived1331 a h
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c365 := h 364 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c841 := derived841 a h
  have h14 : Entails.eval a c179 := h 178 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c1088 := derived1088 a h
  have h17 : Entails.eval a c1319 := derived1319 a h
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1329, some c1251, some c151, some c1118, some c368, some c1287, some c1248, some c96, some c1291, some c841, some c72, some c175, some c367, some c186, some c157, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c1329, c1251, c151, c1118, c368, c1287, c1248, c96, c1291, c841, c72, c175, c367, c186, c157] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c1248 := derived1248 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1291 := derived1291 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1329, some c1333, some c376, some c1287, some c158, some c1288, some c70, some c84, some c162, some c367, some c72, some c163, some c374, some c186, some c169, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c1251, c1329, c1333, c376, c1287, c158, c1288, c70, c84, c162, c367, c72, c163, c374, c186, c169] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1329 := derived1329 a h
  have h2 : Entails.eval a c1333 := derived1333 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c1288 := derived1288 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c1, some c1334, some c1325, some c151, some c499, some c368, some c373, some c92, some c96, some c377, some c374, some c1142, some c175, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c97, c1, c1334, c1325, c151, c499, c368, c373, c92, c96, c377, c374, c1142, c175] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1334 := derived1334 a h
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c499 := derived499 a h
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c373 := h 372 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c1142 := derived1142 a h
  have h13 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1118, some c175, some c363, some c8, some c367, some c157, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1118, c175, c363, c8, c367, c157] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1118 := derived1118 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1298, some c1321, some c1332, some c1335, some c97, some c1, some c1334, some c151, some c499, some c371, some c368, some c1336, some c841, some c374, some c96, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c100, c1298, c1321, c1332, c1335, c97, c1, c1334, c151, c499, c371, c368, c1336, c841, c374, c96] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c1321 := derived1321 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c1335 := derived1335 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c1334 := derived1334 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c499 := derived499 a h
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c1336 := derived1336 a h
  have h13 : Entails.eval a c841 := derived841 a h
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1321, some c1332, some c1, some c158, some c1337, some c100, some c97, some c1298, some c1334, some c946, some c84, some c369, some c366, some c163, some c8, some c1088, some c161, some c1319, some c148, some c146, some c26, some c219, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c1321, c1332, c1, c158, c1337, c100, c97, c1298, c1334, c946, c84, c369, c366, c163, c8, c1088, c161, c1319, c148, c146, c26, c219] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c1321 := derived1321 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c1337 := derived1337 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c1298 := derived1298 a h
  have h8 : Entails.eval a c1334 := derived1334 a h
  have h9 : Entails.eval a c946 := derived946 a h
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c163 := h 162 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c1088 := derived1088 a h
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c1319 := derived1319 a h
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1321, some c1332, some c1, some c158, some c100, some c1298, some c1335, some c841, some c1338, some c365, some c367, some c363, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c1321, c1332, c1, c158, c100, c1298, c1335, c841, c1338, c365, c367, c363] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c1321 := derived1321 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1298 := derived1298 a h
  have h6 : Entails.eval a c1335 := derived1335 a h
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c1338 := derived1338 a h
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1337, some c100, some c1298, some c1321, some c1332, some c1335, some c97, some c1, some c1334, some c158, some c1339, some c71, some c92, some c96, some c365, some c367, some c376, some c163, some c363, some c8, some c374, some c169, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1337, c100, c1298, c1321, c1332, c1335, c97, c1, c1334, c158, c1339, c71, c92, c96, c365, c367, c376, c163, c363, c8, c374, c169] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1337 := derived1337 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1321 := derived1321 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1335 := derived1335 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c1334 := derived1334 a h
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c1339 := derived1339 a h
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c367 := h 366 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c363 := h 362 (by decide)
  have h19 : Entails.eval a c8 := h 7 (by decide)
  have h20 : Entails.eval a c374 := h 373 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨33, by decide⟩, true), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c291, some c299, some c262, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c291, c299, c262] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c291 := h 290 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c946, some c84, some c339, some c366, some c149, some c331, some c1341, some c52, some c48, some c285, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c946, c84, c339, c366, c149, c331, c1341, c52, c48, c285] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c1341 := derived1341 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨13, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c122, some c128, some c191, some c200, some c26, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c281, c122, c128, c191, c200, c26] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1298, some c97, some c100, some c1321, some c1332, some c1, some c1334, some c1335, some c1337, some c1340, some c371, some c368, some c1287, some c376, some c92, some c841, some c363, some c1342, some c367, some c1129, some c157, some c8, some c1031, some c177, some c1343, some c48, some c36, some c283, some c138, some c144, some c191, some c212, some c26, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1298, c97, c100, c1321, c1332, c1, c1334, c1335, c1337, c1340, c371, c368, c1287, c376, c92, c841, c363, c1342, c367, c1129, c157, c8, c1031, c177, c1343, c48, c36, c283, c138, c144, c191, c212, c26] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1298 := derived1298 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1321 := derived1321 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1334 := derived1334 a h
  have h7 : Entails.eval a c1335 := derived1335 a h
  have h8 : Entails.eval a c1337 := derived1337 a h
  have h9 : Entails.eval a c1340 := derived1340 a h
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c1287 := derived1287 a h
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c1342 := derived1342 a h
  have h18 : Entails.eval a c367 := h 366 (by decide)
  have h19 : Entails.eval a c1129 := derived1129 a h
  have h20 : Entails.eval a c157 := h 156 (by decide)
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c1031 := derived1031 a h
  have h23 : Entails.eval a c177 := h 176 (by decide)
  have h24 : Entails.eval a c1343 := derived1343 a h
  have h25 : Entails.eval a c48 := h 47 (by decide)
  have h26 : Entails.eval a c36 := h 35 (by decide)
  have h27 : Entails.eval a c283 := h 282 (by decide)
  have h28 : Entails.eval a c138 := h 137 (by decide)
  have h29 : Entails.eval a c144 := h 143 (by decide)
  have h30 : Entails.eval a c191 := h 190 (by decide)
  have h31 : Entails.eval a c212 := h 211 (by decide)
  have h32 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c172, some c179, some c377, some c182, some c178, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c172, c179, c377, c182, c178] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c172 := h 171 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c841, some c1119, some c367, some c1345, some c373, some c354, some c372, some c160, some c370, some c70, some c1300, some c1309, some c236, some c20, some c24, some c109, some c1035, some c320, some c317, some c385, some c210, some c386, some c135, some c39, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c97, c841, c1119, c367, c1345, c373, c354, c372, c160, c370, c70, c1300, c1309, c236, c20, c24, c109, c1035, c320, c317, c385, c210, c386, c135, c39] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c1119 := derived1119 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c1345 := derived1345 a h
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c1300 := derived1300 a h
  have h12 : Entails.eval a c1309 := derived1309 a h
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c1035 := derived1035 a h
  have h18 : Entails.eval a c320 := h 319 (by decide)
  have h19 : Entails.eval a c317 := h 316 (by decide)
  have h20 : Entails.eval a c385 := derived385 a h
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c386 := derived386 a h
  have h23 : Entails.eval a c135 := h 134 (by decide)
  have h24 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1298, some c97, some c1344, some c80, some c68, some c5, some c1318, some c1346, some c96, some c377, some c173, some c183, some c172, some c1304, some c167, some c367, some c1300, some c1309, some c354, some c236, some c929, some c1303, some c191, some c48, some c127, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c100, c1298, c97, c1344, c80, c68, c5, c1318, c1346, c96, c377, c173, c183, c172, c1304, c167, c367, c1300, c1309, c354, c236, c929, c1303, c191, c48, c127] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c1344 := derived1344 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1318 := derived1318 a h
  have h8 : Entails.eval a c1346 := derived1346 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c172 := h 171 (by decide)
  have h14 : Entails.eval a c1304 := derived1304 a h
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  have h17 : Entails.eval a c1300 := derived1300 a h
  have h18 : Entails.eval a c1309 := derived1309 a h
  have h19 : Entails.eval a c354 := h 353 (by decide)
  have h20 : Entails.eval a c236 := h 235 (by decide)
  have h21 : Entails.eval a c929 := derived929 a h
  have h22 : Entails.eval a c1303 := derived1303 a h
  have h23 : Entails.eval a c191 := h 190 (by decide)
  have h24 : Entails.eval a c48 := h 47 (by decide)
  have h25 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1318, some c5, some c100, some c1344, some c68, some c97, some c80, some c1298, some c1346, some c96, some c377, some c172, some c173, some c183, some c1347, some c372, some c167, some c1300, some c1309, some c236, some c20, some c929, some c191, some c210, some c283, some c135, some c39, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c1318, c5, c100, c1344, c68, c97, c80, c1298, c1346, c96, c377, c172, c173, c183, c1347, c372, c167, c1300, c1309, c236, c20, c929, c191, c210, c283, c135, c39] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c1318 := derived1318 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1344 := derived1344 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c1298 := derived1298 a h
  have h8 : Entails.eval a c1346 := derived1346 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  have h14 : Entails.eval a c1347 := derived1347 a h
  have h15 : Entails.eval a c372 := h 371 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c1300 := derived1300 a h
  have h18 : Entails.eval a c1309 := derived1309 a h
  have h19 : Entails.eval a c236 := h 235 (by decide)
  have h20 : Entails.eval a c20 := h 19 (by decide)
  have h21 : Entails.eval a c929 := derived929 a h
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c283 := h 282 (by decide)
  have h25 : Entails.eval a c135 := h 134 (by decide)
  have h26 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1344, some c68, some c97, some c5, some c1348, some c1325, some c376, some c172, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c100, c1344, c68, c97, c5, c1348, c1325, c376, c172] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c1325 := derived1325 a h
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c372, some c153, some c1138, some c182, some c4, some c1274, some c1300, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c151, c372, c153, c1138, c182, c4, c1274, c1300] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c1138 := derived1138 a h
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c1274 := derived1274 a h
  have h7 : Entails.eval a c1300 := derived1300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c672, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c60, c672] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c300, some c206, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c301, c300, c206] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1349, some c100, some c1344, some c68, some c97, some c80, some c1298, some c151, some c1138, some c372, some c367, some c153, some c1350, some c1323, some c175, some c841, some c96, some c377, some c1309, some c374, some c353, some c236, some c20, some c24, some c251, some c370, some c384, some c1276, some c1351, some c323, some c1036, some c26, some c1352, some c48, some c36, some c288, some c474, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1349, c100, c1344, c68, c97, c80, c1298, c151, c1138, c372, c367, c153, c1350, c1323, c175, c841, c96, c377, c1309, c374, c353, c236, c20, c24, c251, c370, c384, c1276, c1351, c323, c1036, c26, c1352, c48, c36, c288, c474] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1349 := derived1349 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1344 := derived1344 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c1298 := derived1298 a h
  have h7 : Entails.eval a c151 := h 150 (by decide)
  have h8 : Entails.eval a c1138 := derived1138 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c1350 := derived1350 a h
  have h13 : Entails.eval a c1323 := derived1323 a h
  have h14 : Entails.eval a c175 := h 174 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c377 := h 376 (by decide)
  have h18 : Entails.eval a c1309 := derived1309 a h
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c236 := h 235 (by decide)
  have h22 : Entails.eval a c20 := h 19 (by decide)
  have h23 : Entails.eval a c24 := h 23 (by decide)
  have h24 : Entails.eval a c251 := h 250 (by decide)
  have h25 : Entails.eval a c370 := h 369 (by decide)
  have h26 : Entails.eval a c384 := derived384 a h
  have h27 : Entails.eval a c1276 := derived1276 a h
  have h28 : Entails.eval a c1351 := derived1351 a h
  have h29 : Entails.eval a c323 := h 322 (by decide)
  have h30 : Entails.eval a c1036 := derived1036 a h
  have h31 : Entails.eval a c26 := h 25 (by decide)
  have h32 : Entails.eval a c1352 := derived1352 a h
  have h33 : Entails.eval a c48 := h 47 (by decide)
  have h34 : Entails.eval a c36 := h 35 (by decide)
  have h35 : Entails.eval a c288 := h 287 (by decide)
  have h36 : Entails.eval a c474 := derived474 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨35, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨9, by decide⟩, false), (⟨47, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c236, some c20, some c251, some c1351, some c1036, some c326, some c26, some c218, some c212, some c139, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c97, c236, c20, c251, c1351, c1036, c326, c26, c218, c212, c139] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c236 := h 235 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c1351 := derived1351 a h
  have h5 : Entails.eval a c1036 := derived1036 a h
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c115, some c26, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c560, c115, c26] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c1344, some c80, some c1353, some c1325, some c153, some c365, some c68, some c376, some c172, some c1349, some c1298, some c4, some c1031, some c179, some c374, some c353, some c370, some c1276, some c1355, some c20, some c251, some c1354, some c337, some c36, some c301, some c297, some c38, some c202, some c134, some c245, some c211, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c100, c97, c1344, c80, c1353, c1325, c153, c365, c68, c376, c172, c1349, c1298, c4, c1031, c179, c374, c353, c370, c1276, c1355, c20, c251, c1354, c337, c36, c301, c297, c38, c202, c134, c245, c211] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1344 := derived1344 a h
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c1353 := derived1353 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c1349 := derived1349 a h
  have h12 : Entails.eval a c1298 := derived1298 a h
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c1031 := derived1031 a h
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c1276 := derived1276 a h
  have h20 : Entails.eval a c1355 := derived1355 a h
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c251 := h 250 (by decide)
  have h23 : Entails.eval a c1354 := derived1354 a h
  have h24 : Entails.eval a c337 := h 336 (by decide)
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c301 := h 300 (by decide)
  have h27 : Entails.eval a c297 := h 296 (by decide)
  have h28 : Entails.eval a c38 := h 37 (by decide)
  have h29 : Entails.eval a c202 := h 201 (by decide)
  have h30 : Entails.eval a c134 := h 133 (by decide)
  have h31 : Entails.eval a c245 := h 244 (by decide)
  have h32 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c1253, some c1266, some c301, some c341, some c38, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c68, c1253, c1266, c301, c341, c38] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c1253 := derived1253 a h
  have h2 : Entails.eval a c1266 := derived1266 a h
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c1344, some c80, some c1353, some c1325, some c153, some c372, some c1349, some c1298, some c1357, some c4, some c1356, some c163, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c100, c97, c1344, c80, c1353, c1325, c153, c372, c1349, c1298, c1357, c4, c1356, c163] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1344 := derived1344 a h
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c1353 := derived1353 a h
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c1349 := derived1349 a h
  have h9 : Entails.eval a c1298 := derived1298 a h
  have h10 : Entails.eval a c1357 := derived1357 a h
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1356 := derived1356 a h
  have h13 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1344, some c68, some c1298, some c97, some c1349, some c1353, some c1325, some c1358, some c96, some c1274, some c841, some c182, some c179, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c100, c1344, c68, c1298, c97, c1349, c1353, c1325, c1358, c96, c1274, c841, c182, c179] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c1298 := derived1298 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c1349 := derived1349 a h
  have h6 : Entails.eval a c1353 := derived1353 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c1358 := derived1358 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c1274 := derived1274 a h
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c21, some c108, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c26, c21, c108] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c1298, some c1344, some c1357, some c1359, some c68, some c80, some c151, some c170, some c372, some c374, some c153, some c175, some c8, some c1088, some c1360, some c106, some c238, some c237, some c110, some c1352, some c1069, some c36, some c340, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c100, c97, c1298, c1344, c1357, c1359, c68, c80, c151, c170, c372, c374, c153, c175, c8, c1088, c1360, c106, c238, c237, c110, c1352, c1069, c36, c340] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1344 := derived1344 a h
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1359 := derived1359 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c1088 := derived1088 a h
  have h16 : Entails.eval a c1360 := derived1360 a h
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c1352 := derived1352 a h
  have h22 : Entails.eval a c1069 := derived1069 a h
  have h23 : Entails.eval a c36 := h 35 (by decide)
  have h24 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c365, some c158, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c372, c365, c158] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1359, some c100, some c97, some c1344, some c80, some c1298, some c1362, some c153, some c1325, some c1329, some c170, some c1361, some c931, some c373, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c1359, c100, c97, c1344, c80, c1298, c1362, c153, c1325, c1329, c170, c1361, c931, c373] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c1359 := derived1359 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c1344 := derived1344 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c1298 := derived1298 a h
  have h6 : Entails.eval a c1362 := derived1362 a h
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c1325 := derived1325 a h
  have h9 : Entails.eval a c1329 := derived1329 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c1361 := derived1361 a h
  have h12 : Entails.eval a c931 := derived931 a h
  have h13 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨16, by decide⟩, false), (⟨43, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c215, some c283, some c148, some c39, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c191, c215, c283, c148, c39] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c80, some c96, some c377, some c1357, some c173, some c1088, some c1311, some c1309, some c372, some c167, some c1364, some c323, some c60, some c64, some c341, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c68, c80, c96, c377, c1357, c173, c1088, c1311, c1309, c372, c167, c1364, c323, c60, c64, c341] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c173 := h 172 (by decide)
  have h6 : Entails.eval a c1088 := derived1088 a h
  have h7 : Entails.eval a c1311 := derived1311 a h
  have h8 : Entails.eval a c1309 := derived1309 a h
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c1364 := derived1364 a h
  have h12 : Entails.eval a c323 := h 322 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c191, some c283, some c39, some c48, some c342, some c315, some c300, some c210, some c193, some c17, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c97, c191, c283, c39, c48, c342, c315, c300, c210, c193, c17] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c342 := h 341 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c97, some c80, some c1365, some c373, some c1313, some c169, some c149, some c377, some c70, some c1366, some c323, some c709, some c64, some c39, some c314, some c275, some c302, some c189, some c193, some c17, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c68, c97, c80, c1365, c373, c1313, c169, c149, c377, c70, c1366, c323, c709, c64, c39, c314, c275, c302, c189, c193, c17] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c1365 := derived1365 a h
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c1313 := derived1313 a h
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c1366 := derived1366 a h
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c709 := derived709 a h
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c275 := h 274 (by decide)
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1344, some c68, some c97, some c80, some c1298, some c1359, some c1363, some c5, some c1318, some c1367, some c153, some c172, some c372, some c365, some c377, some c157, some c96, some c956, some c841, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c100, c1344, c68, c97, c80, c1298, c1359, c1363, c5, c1318, c1367, c153, c172, c372, c365, c377, c157, c96, c956, c841] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c1298 := derived1298 a h
  have h6 : Entails.eval a c1359 := derived1359 a h
  have h7 : Entails.eval a c1363 := derived1363 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1318 := derived1318 a h
  have h10 : Entails.eval a c1367 := derived1367 a h
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c365 := h 364 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c956 := derived956 a h
  have h19 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c377, some c173, some c100, some c26, some c21, some c105, some c238, some c1352, some c48, some c36, some c130, some c340, some c193, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c373, c377, c173, c100, c26, c21, c105, c238, c1352, c48, c36, c130, c340, c193] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c1352 := derived1352 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1368, some c1, some c10, some c100, some c1344, some c68, some c97, some c80, some c1298, some c1325, some c1329, some c151, some c499, some c373, some c96, some c377, some c374, some c175, some c8, some c1088, some c173, some c1369, some c106, some c1364, some c238, some c237, some c709, some c110, some c1069, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c1368, c1, c10, c100, c1344, c68, c97, c80, c1298, c1325, c1329, c151, c499, c373, c96, c377, c374, c175, c8, c1088, c173, c1369, c106, c1364, c238, c237, c709, c110, c1069] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1344 := derived1344 a h
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c1298 := derived1298 a h
  have h9 : Entails.eval a c1325 := derived1325 a h
  have h10 : Entails.eval a c1329 := derived1329 a h
  have h11 : Entails.eval a c151 := h 150 (by decide)
  have h12 : Entails.eval a c499 := derived499 a h
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c1088 := derived1088 a h
  have h20 : Entails.eval a c173 := h 172 (by decide)
  have h21 : Entails.eval a c1369 := derived1369 a h
  have h22 : Entails.eval a c106 := h 105 (by decide)
  have h23 : Entails.eval a c1364 := derived1364 a h
  have h24 : Entails.eval a c238 := h 237 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c709 := derived709 a h
  have h27 : Entails.eval a c110 := h 109 (by decide)
  have h28 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨54, by decide⟩, false), (⟨13, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c128, some c206, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c301, c128, c206] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨48, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c26, some c21, some c105, some c238, some c1371, some c48, some c288, some c130, some c207, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c100, c26, c21, c105, c238, c1371, c48, c288, c130, c207] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c1371 := derived1371 a h
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨17, by decide⟩, true), (⟨41, by decide⟩, false), (⟨20, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c199, some c275, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c48, c199, c275] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c128, some c200, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c122, c128, c200] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1374, some c36, some c144, some c138, some c212, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1374, c36, c144, c138, c212] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1374 := derived1374 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c165, some c367, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c159, c165, c367] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c26, some c106, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c17, c26, c106] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c8, some c1031, some c1376, some c1375, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c100, c8, c1031, c1376, c1375] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c1031 := derived1031 a h
  have h3 : Entails.eval a c1376 := derived1376 a h
  have h4 : Entails.eval a c1375 := derived1375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1368, some c10, some c1, some c1377, some c1370, some c100, some c97, some c1344, some c80, some c1362, some c68, some c1298, some c96, some c377, some c1357, some c1378, some c1088, some c173, some c169, some c374, some c363, some c367, some c159, some c158, some c1372, some c106, some c111, some c238, some c1364, some c110, some c709, some c1069, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c1368, c10, c1, c1377, c1370, c100, c97, c1344, c80, c1362, c68, c1298, c96, c377, c1357, c1378, c1088, c173, c169, c374, c363, c367, c159, c158, c1372, c106, c111, c238, c1364, c110, c709, c1069] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1377 := derived1377 a h
  have h4 : Entails.eval a c1370 := derived1370 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c1344 := derived1344 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c1362 := derived1362 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c1298 := derived1298 a h
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c1357 := derived1357 a h
  have h15 : Entails.eval a c1378 := derived1378 a h
  have h16 : Entails.eval a c1088 := derived1088 a h
  have h17 : Entails.eval a c173 := h 172 (by decide)
  have h18 : Entails.eval a c169 := h 168 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c363 := h 362 (by decide)
  have h21 : Entails.eval a c367 := h 366 (by decide)
  have h22 : Entails.eval a c159 := h 158 (by decide)
  have h23 : Entails.eval a c158 := h 157 (by decide)
  have h24 : Entails.eval a c1372 := derived1372 a h
  have h25 : Entails.eval a c106 := h 105 (by decide)
  have h26 : Entails.eval a c111 := h 110 (by decide)
  have h27 : Entails.eval a c238 := h 237 (by decide)
  have h28 : Entails.eval a c1364 := derived1364 a h
  have h29 : Entails.eval a c110 := h 109 (by decide)
  have h30 : Entails.eval a c709 := derived709 a h
  have h31 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨44, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c80, some c1378, some c1253, some c1266, some c122, some c128, some c144, some c138, some c264, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c100, c80, c1378, c1253, c1266, c122, c128, c144, c138, c264] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c1378 := derived1378 a h
  have h3 : Entails.eval a c1253 := derived1253 a h
  have h4 : Entails.eval a c1266 := derived1266 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1380

end CochromaticTwenty.Certificates.B16_8_2
