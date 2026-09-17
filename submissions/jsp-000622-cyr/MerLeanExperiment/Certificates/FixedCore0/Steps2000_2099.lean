import MerLeanExperiment.Certificates.FixedCore0.Steps1900_1999

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9551 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9551 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2565, some c2560, some c3754, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9551 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9551 : lratChecker f9551 p9551 = .success := by decide +kernel
theorem unsat9551 : Unsatisfiable (PosFin 65) f9551 := by
  apply lratCheckerSound f9551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9551
  · intro a ha; simp [p9551] at ha; subst a; trivial
  · exact checked9551
theorem derived9551 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9551 := by
  apply localUnsat_implies_entails f9551 [c2565, c2560, c3754] c9551 unsat9551 (by rfl) a
  have h0 : Entails.eval a c2565 := h 2564 (by decide)
  have h1 : Entails.eval a c2560 := h 2559 (by decide)
  have h2 : Entails.eval a c3754 := h 3753 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9552 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9552 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8826, some c1182, some c616, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9552 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9552 : lratChecker f9552 p9552 = .success := by decide +kernel
theorem unsat9552 : Unsatisfiable (PosFin 65) f9552 := by
  apply lratCheckerSound f9552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9552
  · intro a ha; simp [p9552] at ha; subst a; trivial
  · exact checked9552
theorem derived9552 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9552 := by
  apply localUnsat_implies_entails f9552 [c8826, c1182, c616] c9552 unsat9552 (by rfl) a
  have h0 : Entails.eval a c8826 := derived8826 a h
  have h1 : Entails.eval a c1182 := h 1181 (by decide)
  have h2 : Entails.eval a c616 := h 615 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9553 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9553 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9534, some c9494, some c9347, some c9550, some c9552, some c1261, some c9551, some c3032, some c1198, some c3031, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9553 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9553 : lratChecker f9553 p9553 = .success := by decide +kernel
theorem unsat9553 : Unsatisfiable (PosFin 65) f9553 := by
  apply lratCheckerSound f9553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9553
  · intro a ha; simp [p9553] at ha; subst a; trivial
  · exact checked9553
theorem derived9553 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9553 := by
  apply localUnsat_implies_entails f9553 [c9115, c9534, c9494, c9347, c9550, c9552, c1261, c9551, c3032, c1198, c3031] c9553 unsat9553 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9550 := derived9550 a h
  have h5 : Entails.eval a c9552 := derived9552 a h
  have h6 : Entails.eval a c1261 := h 1260 (by decide)
  have h7 : Entails.eval a c9551 := derived9551 a h
  have h8 : Entails.eval a c3032 := h 3031 (by decide)
  have h9 : Entails.eval a c1198 := h 1197 (by decide)
  have h10 : Entails.eval a c3031 := h 3030 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9554 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9554 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c1286, some c1285, some c1300, some c9534, some c9553, some c1180, some c1250, some c3757, some c3758, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9554 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9554 : lratChecker f9554 p9554 = .success := by decide +kernel
theorem unsat9554 : Unsatisfiable (PosFin 65) f9554 := by
  apply lratCheckerSound f9554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9554
  · intro a ha; simp [p9554] at ha; subst a; trivial
  · exact checked9554
theorem derived9554 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9554 := by
  apply localUnsat_implies_entails f9554 [c9494, c1286, c1285, c1300, c9534, c9553, c1180, c1250, c3757, c3758] c9554 unsat9554 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c1286 := h 1285 (by decide)
  have h2 : Entails.eval a c1285 := h 1284 (by decide)
  have h3 : Entails.eval a c1300 := h 1299 (by decide)
  have h4 : Entails.eval a c9534 := derived9534 a h
  have h5 : Entails.eval a c9553 := derived9553 a h
  have h6 : Entails.eval a c1180 := h 1179 (by decide)
  have h7 : Entails.eval a c1250 := h 1249 (by decide)
  have h8 : Entails.eval a c3757 := h 3756 (by decide)
  have h9 : Entails.eval a c3758 := h 3757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9555 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9555 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1261, some c3428, some c3399, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9555 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9555 : lratChecker f9555 p9555 = .success := by decide +kernel
theorem unsat9555 : Unsatisfiable (PosFin 65) f9555 := by
  apply lratCheckerSound f9555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9555
  · intro a ha; simp [p9555] at ha; subst a; trivial
  · exact checked9555
theorem derived9555 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9555 := by
  apply localUnsat_implies_entails f9555 [c1261, c3428, c3399] c9555 unsat9555 (by rfl) a
  have h0 : Entails.eval a c1261 := h 1260 (by decide)
  have h1 : Entails.eval a c3428 := h 3427 (by decide)
  have h2 : Entails.eval a c3399 := h 3398 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9556 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9556 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9534, some c9154, some c9494, some c1286, some c1285, some c1300, some c1272, some c1303, some c9554, some c9555, some c8826, some c8818, some c3399, some c3427, some c3430, some c3397, some c610, some c1255, some c1193, some c3426, some c1243, some c367, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9556 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9556 : lratChecker f9556 p9556 = .success := by decide +kernel
theorem unsat9556 : Unsatisfiable (PosFin 65) f9556 := by
  apply lratCheckerSound f9556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9556
  · intro a ha; simp [p9556] at ha; subst a; trivial
  · exact checked9556
theorem derived9556 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9556 := by
  apply localUnsat_implies_entails f9556 [c9115, c9534, c9154, c9494, c1286, c1285, c1300, c1272, c1303, c9554, c9555, c8826, c8818, c3399, c3427, c3430, c3397, c610, c1255, c1193, c3426, c1243, c367] c9556 unsat9556 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9154 := derived9154 a h
  have h3 : Entails.eval a c9494 := derived9494 a h
  have h4 : Entails.eval a c1286 := h 1285 (by decide)
  have h5 : Entails.eval a c1285 := h 1284 (by decide)
  have h6 : Entails.eval a c1300 := h 1299 (by decide)
  have h7 : Entails.eval a c1272 := h 1271 (by decide)
  have h8 : Entails.eval a c1303 := h 1302 (by decide)
  have h9 : Entails.eval a c9554 := derived9554 a h
  have h10 : Entails.eval a c9555 := derived9555 a h
  have h11 : Entails.eval a c8826 := derived8826 a h
  have h12 : Entails.eval a c8818 := derived8818 a h
  have h13 : Entails.eval a c3399 := h 3398 (by decide)
  have h14 : Entails.eval a c3427 := h 3426 (by decide)
  have h15 : Entails.eval a c3430 := h 3429 (by decide)
  have h16 : Entails.eval a c3397 := h 3396 (by decide)
  have h17 : Entails.eval a c610 := h 609 (by decide)
  have h18 : Entails.eval a c1255 := h 1254 (by decide)
  have h19 : Entails.eval a c1193 := h 1192 (by decide)
  have h20 : Entails.eval a c3426 := h 3425 (by decide)
  have h21 : Entails.eval a c1243 := h 1242 (by decide)
  have h22 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9557 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9557 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8812, some c1175, some c1176, some c637, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9557 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9557 : lratChecker f9557 p9557 = .success := by decide +kernel
theorem unsat9557 : Unsatisfiable (PosFin 65) f9557 := by
  apply lratCheckerSound f9557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9557
  · intro a ha; simp [p9557] at ha; subst a; trivial
  · exact checked9557
theorem derived9557 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9557 := by
  apply localUnsat_implies_entails f9557 [c8812, c1175, c1176, c637] c9557 unsat9557 (by rfl) a
  have h0 : Entails.eval a c8812 := derived8812 a h
  have h1 : Entails.eval a c1175 := h 1174 (by decide)
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9558 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9558 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1261, some c8745, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9558 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9558 : lratChecker f9558 p9558 = .success := by decide +kernel
theorem unsat9558 : Unsatisfiable (PosFin 65) f9558 := by
  apply lratCheckerSound f9558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9558
  · intro a ha; simp [p9558] at ha; subst a; trivial
  · exact checked9558
theorem derived9558 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9558 := by
  apply localUnsat_implies_entails f9558 [c1261, c8745] c9558 unsat9558 (by rfl) a
  have h0 : Entails.eval a c1261 := h 1260 (by decide)
  have h1 : Entails.eval a c8745 := derived8745 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9559 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9559 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9546, some c9534, some c9494, some c9154, some c9152, some c1235, some c1272, some c1285, some c1286, some c1303, some c1300, some c1222, some c9549, some c9115, some c9557, some c9556, some c9558, some c8826, some c8818, some c852, some c851, some c640, some c859, some c1244, some c9552, some c1243, some c1266, some c92, some c1208, some c7551, some c873, some c284, some c5779, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9559 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked9559 : lratChecker f9559 p9559 = .success := by decide +kernel
theorem unsat9559 : Unsatisfiable (PosFin 65) f9559 := by
  apply lratCheckerSound f9559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9559
  · intro a ha; simp [p9559] at ha; subst a; trivial
  · exact checked9559
theorem derived9559 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9559 := by
  apply localUnsat_implies_entails f9559 [c9546, c9534, c9494, c9154, c9152, c1235, c1272, c1285, c1286, c1303, c1300, c1222, c9549, c9115, c9557, c9556, c9558, c8826, c8818, c852, c851, c640, c859, c1244, c9552, c1243, c1266, c92, c1208, c7551, c873, c284, c5779] c9559 unsat9559 (by rfl) a
  have h0 : Entails.eval a c9546 := derived9546 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9154 := derived9154 a h
  have h4 : Entails.eval a c9152 := derived9152 a h
  have h5 : Entails.eval a c1235 := h 1234 (by decide)
  have h6 : Entails.eval a c1272 := h 1271 (by decide)
  have h7 : Entails.eval a c1285 := h 1284 (by decide)
  have h8 : Entails.eval a c1286 := h 1285 (by decide)
  have h9 : Entails.eval a c1303 := h 1302 (by decide)
  have h10 : Entails.eval a c1300 := h 1299 (by decide)
  have h11 : Entails.eval a c1222 := h 1221 (by decide)
  have h12 : Entails.eval a c9549 := derived9549 a h
  have h13 : Entails.eval a c9115 := derived9115 a h
  have h14 : Entails.eval a c9557 := derived9557 a h
  have h15 : Entails.eval a c9556 := derived9556 a h
  have h16 : Entails.eval a c9558 := derived9558 a h
  have h17 : Entails.eval a c8826 := derived8826 a h
  have h18 : Entails.eval a c8818 := derived8818 a h
  have h19 : Entails.eval a c852 := h 851 (by decide)
  have h20 : Entails.eval a c851 := h 850 (by decide)
  have h21 : Entails.eval a c640 := h 639 (by decide)
  have h22 : Entails.eval a c859 := h 858 (by decide)
  have h23 : Entails.eval a c1244 := h 1243 (by decide)
  have h24 : Entails.eval a c9552 := derived9552 a h
  have h25 : Entails.eval a c1243 := h 1242 (by decide)
  have h26 : Entails.eval a c1266 := h 1265 (by decide)
  have h27 : Entails.eval a c92 := h 91 (by decide)
  have h28 : Entails.eval a c1208 := h 1207 (by decide)
  have h29 : Entails.eval a c7551 := derived7551 a h
  have h30 : Entails.eval a c873 := h 872 (by decide)
  have h31 : Entails.eval a c284 := h 283 (by decide)
  have h32 : Entails.eval a c5779 := h 5778 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9560 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9560 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2531, some c2550, some c2682, some c3769, some c4088, some c3082, some c3083, some c3092, some c3162, some c4344, some c4377, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9560 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9560 : lratChecker f9560 p9560 = .success := by decide +kernel
theorem unsat9560 : Unsatisfiable (PosFin 65) f9560 := by
  apply lratCheckerSound f9560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9560
  · intro a ha; simp [p9560] at ha; subst a; trivial
  · exact checked9560
theorem derived9560 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9560 := by
  apply localUnsat_implies_entails f9560 [c2531, c2550, c2682, c3769, c4088, c3082, c3083, c3092, c3162, c4344, c4377] c9560 unsat9560 (by rfl) a
  have h0 : Entails.eval a c2531 := h 2530 (by decide)
  have h1 : Entails.eval a c2550 := h 2549 (by decide)
  have h2 : Entails.eval a c2682 := h 2681 (by decide)
  have h3 : Entails.eval a c3769 := h 3768 (by decide)
  have h4 : Entails.eval a c4088 := h 4087 (by decide)
  have h5 : Entails.eval a c3082 := h 3081 (by decide)
  have h6 : Entails.eval a c3083 := h 3082 (by decide)
  have h7 : Entails.eval a c3092 := h 3091 (by decide)
  have h8 : Entails.eval a c3162 := h 3161 (by decide)
  have h9 : Entails.eval a c4344 := h 4343 (by decide)
  have h10 : Entails.eval a c4377 := h 4376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9561 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9561 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c2661, some c2659, some c1249, some c2541, some c3413, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9561 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9561 : lratChecker f9561 p9561 = .success := by decide +kernel
theorem unsat9561 : Unsatisfiable (PosFin 65) f9561 := by
  apply lratCheckerSound f9561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9561
  · intro a ha; simp [p9561] at ha; subst a; trivial
  · exact checked9561
theorem derived9561 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9561 := by
  apply localUnsat_implies_entails f9561 [c9347, c2661, c2659, c1249, c2541, c3413] c9561 unsat9561 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c2661 := h 2660 (by decide)
  have h2 : Entails.eval a c2659 := h 2658 (by decide)
  have h3 : Entails.eval a c1249 := h 1248 (by decide)
  have h4 : Entails.eval a c2541 := h 2540 (by decide)
  have h5 : Entails.eval a c3413 := h 3412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9562 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9562 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2667, some c2666, some c2658, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9562 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9562 : lratChecker f9562 p9562 = .success := by decide +kernel
theorem unsat9562 : Unsatisfiable (PosFin 65) f9562 := by
  apply lratCheckerSound f9562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9562
  · intro a ha; simp [p9562] at ha; subst a; trivial
  · exact checked9562
theorem derived9562 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9562 := by
  apply localUnsat_implies_entails f9562 [c2667, c2666, c2658] c9562 unsat9562 (by rfl) a
  have h0 : Entails.eval a c2667 := h 2666 (by decide)
  have h1 : Entails.eval a c2666 := h 2665 (by decide)
  have h2 : Entails.eval a c2658 := h 2657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9563 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9563 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9347, some c9561, some c8826, some c9562, some c618, some c1263, some c610, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9563 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9563 : lratChecker f9563 p9563 = .success := by decide +kernel
theorem unsat9563 : Unsatisfiable (PosFin 65) f9563 := by
  apply lratCheckerSound f9563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9563
  · intro a ha; simp [p9563] at ha; subst a; trivial
  · exact checked9563
theorem derived9563 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9563 := by
  apply localUnsat_implies_entails f9563 [c9115, c9347, c9561, c8826, c9562, c618, c1263, c610] c9563 unsat9563 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9561 := derived9561 a h
  have h3 : Entails.eval a c8826 := derived8826 a h
  have h4 : Entails.eval a c9562 := derived9562 a h
  have h5 : Entails.eval a c618 := h 617 (by decide)
  have h6 : Entails.eval a c1263 := h 1262 (by decide)
  have h7 : Entails.eval a c610 := h 609 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9564 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9564 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1286, some c1285, some c1300, some c1272, some c1303, some c9115, some c9558, some c8818, some c8826, some c852, some c851, some c640, some c859, some c1244, some c856, some c854, some c1243, some c1266, some c197, some c198, some c7551, some c872, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9564 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9564 : lratChecker f9564 p9564 = .success := by decide +kernel
theorem unsat9564 : Unsatisfiable (PosFin 65) f9564 := by
  apply lratCheckerSound f9564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9564
  · intro a ha; simp [p9564] at ha; subst a; trivial
  · exact checked9564
theorem derived9564 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9564 := by
  apply localUnsat_implies_entails f9564 [c1286, c1285, c1300, c1272, c1303, c9115, c9558, c8818, c8826, c852, c851, c640, c859, c1244, c856, c854, c1243, c1266, c197, c198, c7551, c872] c9564 unsat9564 (by rfl) a
  have h0 : Entails.eval a c1286 := h 1285 (by decide)
  have h1 : Entails.eval a c1285 := h 1284 (by decide)
  have h2 : Entails.eval a c1300 := h 1299 (by decide)
  have h3 : Entails.eval a c1272 := h 1271 (by decide)
  have h4 : Entails.eval a c1303 := h 1302 (by decide)
  have h5 : Entails.eval a c9115 := derived9115 a h
  have h6 : Entails.eval a c9558 := derived9558 a h
  have h7 : Entails.eval a c8818 := derived8818 a h
  have h8 : Entails.eval a c8826 := derived8826 a h
  have h9 : Entails.eval a c852 := h 851 (by decide)
  have h10 : Entails.eval a c851 := h 850 (by decide)
  have h11 : Entails.eval a c640 := h 639 (by decide)
  have h12 : Entails.eval a c859 := h 858 (by decide)
  have h13 : Entails.eval a c1244 := h 1243 (by decide)
  have h14 : Entails.eval a c856 := h 855 (by decide)
  have h15 : Entails.eval a c854 := h 853 (by decide)
  have h16 : Entails.eval a c1243 := h 1242 (by decide)
  have h17 : Entails.eval a c1266 := h 1265 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c198 := h 197 (by decide)
  have h20 : Entails.eval a c7551 := derived7551 a h
  have h21 : Entails.eval a c872 := h 871 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9565 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9565 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1272, some c1285, some c1286, some c1303, some c1300, some c9563, some c9564, some c8812, some c1245, some c1246, some c637, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9565 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9565 : lratChecker f9565 p9565 = .success := by decide +kernel
theorem unsat9565 : Unsatisfiable (PosFin 65) f9565 := by
  apply lratCheckerSound f9565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9565
  · intro a ha; simp [p9565] at ha; subst a; trivial
  · exact checked9565
theorem derived9565 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9565 := by
  apply localUnsat_implies_entails f9565 [c1272, c1285, c1286, c1303, c1300, c9563, c9564, c8812, c1245, c1246, c637] c9565 unsat9565 (by rfl) a
  have h0 : Entails.eval a c1272 := h 1271 (by decide)
  have h1 : Entails.eval a c1285 := h 1284 (by decide)
  have h2 : Entails.eval a c1286 := h 1285 (by decide)
  have h3 : Entails.eval a c1303 := h 1302 (by decide)
  have h4 : Entails.eval a c1300 := h 1299 (by decide)
  have h5 : Entails.eval a c9563 := derived9563 a h
  have h6 : Entails.eval a c9564 := derived9564 a h
  have h7 : Entails.eval a c8812 := derived8812 a h
  have h8 : Entails.eval a c1245 := h 1244 (by decide)
  have h9 : Entails.eval a c1246 := h 1245 (by decide)
  have h10 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9566 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9566 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2693, some c2672, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9566 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9566 : lratChecker f9566 p9566 = .success := by decide +kernel
theorem unsat9566 : Unsatisfiable (PosFin 65) f9566 := by
  apply lratCheckerSound f9566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9566
  · intro a ha; simp [p9566] at ha; subst a; trivial
  · exact checked9566
theorem derived9566 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9566 := by
  apply localUnsat_implies_entails f9566 [c2693, c2672] c9566 unsat9566 (by rfl) a
  have h0 : Entails.eval a c2693 := h 2692 (by decide)
  have h1 : Entails.eval a c2672 := h 2671 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9567 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9567 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c1290, some c1289, some c3188, some c3774, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9567 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9567 : lratChecker f9567 p9567 = .success := by decide +kernel
theorem unsat9567 : Unsatisfiable (PosFin 65) f9567 := by
  apply lratCheckerSound f9567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9567
  · intro a ha; simp [p9567] at ha; subst a; trivial
  · exact checked9567
theorem derived9567 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9567 := by
  apply localUnsat_implies_entails f9567 [c9534, c9494, c1290, c1289, c3188, c3774] c9567 unsat9567 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c1290 := h 1289 (by decide)
  have h3 : Entails.eval a c1289 := h 1288 (by decide)
  have h4 : Entails.eval a c3188 := h 3187 (by decide)
  have h5 : Entails.eval a c3774 := h 3773 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9568 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9568 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9558, some c8818, some c852, some c851, some c859, some c202, some c206, some c201, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9568 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9568 : lratChecker f9568 p9568 = .success := by decide +kernel
theorem unsat9568 : Unsatisfiable (PosFin 65) f9568 := by
  apply lratCheckerSound f9568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9568
  · intro a ha; simp [p9568] at ha; subst a; trivial
  · exact checked9568
theorem derived9568 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9568 := by
  apply localUnsat_implies_entails f9568 [c9115, c9558, c8818, c852, c851, c859, c202, c206, c201] c9568 unsat9568 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9558 := derived9558 a h
  have h2 : Entails.eval a c8818 := derived8818 a h
  have h3 : Entails.eval a c852 := h 851 (by decide)
  have h4 : Entails.eval a c851 := h 850 (by decide)
  have h5 : Entails.eval a c859 := h 858 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9569 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9569 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9115, some c9534, some c9494, some c9568, some c8812, some c8715, some c852, some c3427, some c3749, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9569 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9569 : lratChecker f9569 p9569 = .success := by decide +kernel
theorem unsat9569 : Unsatisfiable (PosFin 65) f9569 := by
  apply lratCheckerSound f9569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9569
  · intro a ha; simp [p9569] at ha; subst a; trivial
  · exact checked9569
theorem derived9569 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9569 := by
  apply localUnsat_implies_entails f9569 [c9115, c9534, c9494, c9568, c8812, c8715, c852, c3427, c3749] c9569 unsat9569 (by rfl) a
  have h0 : Entails.eval a c9115 := derived9115 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9568 := derived9568 a h
  have h4 : Entails.eval a c8812 := derived8812 a h
  have h5 : Entails.eval a c8715 := derived8715 a h
  have h6 : Entails.eval a c852 := h 851 (by decide)
  have h7 : Entails.eval a c3427 := h 3426 (by decide)
  have h8 : Entails.eval a c3749 := h 3748 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9570 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9570 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9546, some c9534, some c9494, some c9347, some c9559, some c9508, some c1292, some c9560, some c9565, some c9566, some c9567, some c9569, some c1300, some c1299, some c1287, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9570 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9570 : lratChecker f9570 p9570 = .success := by decide +kernel
theorem unsat9570 : Unsatisfiable (PosFin 65) f9570 := by
  apply lratCheckerSound f9570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9570
  · intro a ha; simp [p9570] at ha; subst a; trivial
  · exact checked9570
theorem derived9570 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9570 := by
  apply localUnsat_implies_entails f9570 [c9546, c9534, c9494, c9347, c9559, c9508, c1292, c9560, c9565, c9566, c9567, c9569, c1300, c1299, c1287] c9570 unsat9570 (by rfl) a
  have h0 : Entails.eval a c9546 := derived9546 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9559 := derived9559 a h
  have h5 : Entails.eval a c9508 := derived9508 a h
  have h6 : Entails.eval a c1292 := h 1291 (by decide)
  have h7 : Entails.eval a c9560 := derived9560 a h
  have h8 : Entails.eval a c9565 := derived9565 a h
  have h9 : Entails.eval a c9566 := derived9566 a h
  have h10 : Entails.eval a c9567 := derived9567 a h
  have h11 : Entails.eval a c9569 := derived9569 a h
  have h12 : Entails.eval a c1300 := h 1299 (by decide)
  have h13 : Entails.eval a c1299 := h 1298 (by decide)
  have h14 : Entails.eval a c1287 := h 1286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9571 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9571 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c1279, some c9356, some c1272, some c2172, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9571 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9571 : lratChecker f9571 p9571 = .success := by decide +kernel
theorem unsat9571 : Unsatisfiable (PosFin 65) f9571 := by
  apply lratCheckerSound f9571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9571
  · intro a ha; simp [p9571] at ha; subst a; trivial
  · exact checked9571
theorem derived9571 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9571 := by
  apply localUnsat_implies_entails f9571 [c9347, c1279, c9356, c1272, c2172] c9571 unsat9571 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c1279 := h 1278 (by decide)
  have h2 : Entails.eval a c9356 := derived9356 a h
  have h3 : Entails.eval a c1272 := h 1271 (by decide)
  have h4 : Entails.eval a c2172 := h 2171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9572 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9572 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9571, some c9406, some c2172, some c2169, some c1285, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9572 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9572 : lratChecker f9572 p9572 = .success := by decide +kernel
theorem unsat9572 : Unsatisfiable (PosFin 65) f9572 := by
  apply lratCheckerSound f9572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9572
  · intro a ha; simp [p9572] at ha; subst a; trivial
  · exact checked9572
theorem derived9572 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9572 := by
  apply localUnsat_implies_entails f9572 [c9347, c9571, c9406, c2172, c2169, c1285] c9572 unsat9572 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9571 := derived9571 a h
  have h2 : Entails.eval a c9406 := derived9406 a h
  have h3 : Entails.eval a c2172 := h 2171 (by decide)
  have h4 : Entails.eval a c2169 := h 2168 (by decide)
  have h5 : Entails.eval a c1285 := h 1284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9573 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9573 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1261, some c8818, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9573 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9573 : lratChecker f9573 p9573 = .success := by decide +kernel
theorem unsat9573 : Unsatisfiable (PosFin 65) f9573 := by
  apply lratCheckerSound f9573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9573
  · intro a ha; simp [p9573] at ha; subst a; trivial
  · exact checked9573
theorem derived9573 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9573 := by
  apply localUnsat_implies_entails f9573 [c1261, c8818] c9573 unsat9573 (by rfl) a
  have h0 : Entails.eval a c1261 := h 1260 (by decide)
  have h1 : Entails.eval a c8818 := derived8818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9574 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9574 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8715, some c9573, some c8812, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9574 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9574 : lratChecker f9574 p9574 = .success := by decide +kernel
theorem unsat9574 : Unsatisfiable (PosFin 65) f9574 := by
  apply lratCheckerSound f9574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9574
  · intro a ha; simp [p9574] at ha; subst a; trivial
  · exact checked9574
theorem derived9574 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9574 := by
  apply localUnsat_implies_entails f9574 [c8715, c9573, c8812] c9574 unsat9574 (by rfl) a
  have h0 : Entails.eval a c8715 := derived8715 a h
  have h1 : Entails.eval a c9573 := derived9573 a h
  have h2 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9575 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9575 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9572, some c9574, some c9115, some c9347, some c1292, some c9356, some c8763, some c722, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9575 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9575 : lratChecker f9575 p9575 = .success := by decide +kernel
theorem unsat9575 : Unsatisfiable (PosFin 65) f9575 := by
  apply lratCheckerSound f9575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9575
  · intro a ha; simp [p9575] at ha; subst a; trivial
  · exact checked9575
theorem derived9575 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9575 := by
  apply localUnsat_implies_entails f9575 [c9572, c9574, c9115, c9347, c1292, c9356, c8763, c722] c9575 unsat9575 (by rfl) a
  have h0 : Entails.eval a c9572 := derived9572 a h
  have h1 : Entails.eval a c9574 := derived9574 a h
  have h2 : Entails.eval a c9115 := derived9115 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c1292 := h 1291 (by decide)
  have h5 : Entails.eval a c9356 := derived9356 a h
  have h6 : Entails.eval a c8763 := derived8763 a h
  have h7 : Entails.eval a c722 := h 721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9576 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9576 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1272, some c1285, some c1283, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9576 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9576 : lratChecker f9576 p9576 = .success := by decide +kernel
theorem unsat9576 : Unsatisfiable (PosFin 65) f9576 := by
  apply lratCheckerSound f9576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9576
  · intro a ha; simp [p9576] at ha; subst a; trivial
  · exact checked9576
theorem derived9576 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9576 := by
  apply localUnsat_implies_entails f9576 [c1272, c1285, c1283] c9576 unsat9576 (by rfl) a
  have h0 : Entails.eval a c1272 := h 1271 (by decide)
  have h1 : Entails.eval a c1285 := h 1284 (by decide)
  have h2 : Entails.eval a c1283 := h 1282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9577 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9577 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c9347, some c9546, some c9570, some c9381, some c9572, some c9575, some c9576, some c1280, some c9477, some c2171, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9577 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9577 : lratChecker f9577 p9577 = .success := by decide +kernel
theorem unsat9577 : Unsatisfiable (PosFin 65) f9577 := by
  apply lratCheckerSound f9577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9577
  · intro a ha; simp [p9577] at ha; subst a; trivial
  · exact checked9577
theorem derived9577 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9577 := by
  apply localUnsat_implies_entails f9577 [c9534, c9494, c9347, c9546, c9570, c9381, c9572, c9575, c9576, c1280, c9477, c2171] c9577 unsat9577 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9546 := derived9546 a h
  have h4 : Entails.eval a c9570 := derived9570 a h
  have h5 : Entails.eval a c9381 := derived9381 a h
  have h6 : Entails.eval a c9572 := derived9572 a h
  have h7 : Entails.eval a c9575 := derived9575 a h
  have h8 : Entails.eval a c9576 := derived9576 a h
  have h9 : Entails.eval a c1280 := h 1279 (by decide)
  have h10 : Entails.eval a c9477 := derived9477 a h
  have h11 : Entails.eval a c2171 := h 2170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9578 : DefaultClause 65 := directClause [(⟨58, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9578 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2506, some c4944, some (DefaultClause.unit (⟨58, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9578 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9578 : lratChecker f9578 p9578 = .success := by decide +kernel
theorem unsat9578 : Unsatisfiable (PosFin 65) f9578 := by
  apply lratCheckerSound f9578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9578
  · intro a ha; simp [p9578] at ha; subst a; trivial
  · exact checked9578
theorem derived9578 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9578 := by
  apply localUnsat_implies_entails f9578 [c2506, c4944] c9578 unsat9578 (by rfl) a
  have h0 : Entails.eval a c2506 := h 2505 (by decide)
  have h1 : Entails.eval a c4944 := h 4943 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9579 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨13, by decide⟩, false), (⟨58, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9579 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3769, some c5105, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9579 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9579 : lratChecker f9579 p9579 = .success := by decide +kernel
theorem unsat9579 : Unsatisfiable (PosFin 65) f9579 := by
  apply lratCheckerSound f9579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9579
  · intro a ha; simp [p9579] at ha; subst a; trivial
  · exact checked9579
theorem derived9579 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9579 := by
  apply localUnsat_implies_entails f9579 [c3769, c5105] c9579 unsat9579 (by rfl) a
  have h0 : Entails.eval a c3769 := h 3768 (by decide)
  have h1 : Entails.eval a c5105 := h 5104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9580 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9580 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9577, some c9217, some c9494, some c9347, some c9324, some c9578, some c3010, some c9228, some c9579, some c2170, some c2469, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9580 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9580 : lratChecker f9580 p9580 = .success := by decide +kernel
theorem unsat9580 : Unsatisfiable (PosFin 65) f9580 := by
  apply lratCheckerSound f9580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9580
  · intro a ha; simp [p9580] at ha; subst a; trivial
  · exact checked9580
theorem derived9580 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9580 := by
  apply localUnsat_implies_entails f9580 [c9534, c9577, c9217, c9494, c9347, c9324, c9578, c3010, c9228, c9579, c2170, c2469] c9580 unsat9580 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9577 := derived9577 a h
  have h2 : Entails.eval a c9217 := derived9217 a h
  have h3 : Entails.eval a c9494 := derived9494 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9324 := derived9324 a h
  have h6 : Entails.eval a c9578 := derived9578 a h
  have h7 : Entails.eval a c3010 := h 3009 (by decide)
  have h8 : Entails.eval a c9228 := derived9228 a h
  have h9 : Entails.eval a c9579 := derived9579 a h
  have h10 : Entails.eval a c2170 := h 2169 (by decide)
  have h11 : Entails.eval a c2469 := h 2468 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9581 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9581 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2460, some c3229, some c2404, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9581 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9581 : lratChecker f9581 p9581 = .success := by decide +kernel
theorem unsat9581 : Unsatisfiable (PosFin 65) f9581 := by
  apply lratCheckerSound f9581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9581
  · intro a ha; simp [p9581] at ha; subst a; trivial
  · exact checked9581
theorem derived9581 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9581 := by
  apply localUnsat_implies_entails f9581 [c2460, c3229, c2404] c9581 unsat9581 (by rfl) a
  have h0 : Entails.eval a c2460 := h 2459 (by decide)
  have h1 : Entails.eval a c3229 := h 3228 (by decide)
  have h2 : Entails.eval a c2404 := h 2403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9582 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨10, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9582 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3278, some c5835, some c2464, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9582 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9582 : lratChecker f9582 p9582 = .success := by decide +kernel
theorem unsat9582 : Unsatisfiable (PosFin 65) f9582 := by
  apply lratCheckerSound f9582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9582
  · intro a ha; simp [p9582] at ha; subst a; trivial
  · exact checked9582
theorem derived9582 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9582 := by
  apply localUnsat_implies_entails f9582 [c3278, c5835, c2464] c9582 unsat9582 (by rfl) a
  have h0 : Entails.eval a c3278 := h 3277 (by decide)
  have h1 : Entails.eval a c5835 := h 5834 (by decide)
  have h2 : Entails.eval a c2464 := h 2463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9583 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9583 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2407, some c2409, some c2406, some c2405, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p9583 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9583 : lratChecker f9583 p9583 = .success := by decide +kernel
theorem unsat9583 : Unsatisfiable (PosFin 65) f9583 := by
  apply lratCheckerSound f9583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9583
  · intro a ha; simp [p9583] at ha; subst a; trivial
  · exact checked9583
theorem derived9583 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9583 := by
  apply localUnsat_implies_entails f9583 [c2407, c2409, c2406, c2405] c9583 unsat9583 (by rfl) a
  have h0 : Entails.eval a c2407 := h 2406 (by decide)
  have h1 : Entails.eval a c2409 := h 2408 (by decide)
  have h2 : Entails.eval a c2406 := h 2405 (by decide)
  have h3 : Entails.eval a c2405 := h 2404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9584 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨51, by decide⟩, true), (⟨61, by decide⟩, true), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9584 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9581, some c9582, some c9583, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9584 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9584 : lratChecker f9584 p9584 = .success := by decide +kernel
theorem unsat9584 : Unsatisfiable (PosFin 65) f9584 := by
  apply lratCheckerSound f9584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9584
  · intro a ha; simp [p9584] at ha; subst a; trivial
  · exact checked9584
theorem derived9584 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9584 := by
  apply localUnsat_implies_entails f9584 [c9581, c9582, c9583] c9584 unsat9584 (by rfl) a
  have h0 : Entails.eval a c9581 := derived9581 a h
  have h1 : Entails.eval a c9582 := derived9582 a h
  have h2 : Entails.eval a c9583 := derived9583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9585 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9585 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9577, some c9534, some c9580, some c2999, some c3022, some c9347, some c9217, some c3013, some c2425, some c2440, some c3018, some c9494, some c2175, some c3770, some c2532, some c2551, some c9547, some c4088, some c9584, some c9332, some c3213, some c205, some c3214, some c2985, some c3278, some c3217, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9585 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9585 : lratChecker f9585 p9585 = .success := by decide +kernel
theorem unsat9585 : Unsatisfiable (PosFin 65) f9585 := by
  apply lratCheckerSound f9585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9585
  · intro a ha; simp [p9585] at ha; subst a; trivial
  · exact checked9585
theorem derived9585 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9585 := by
  apply localUnsat_implies_entails f9585 [c9577, c9534, c9580, c2999, c3022, c9347, c9217, c3013, c2425, c2440, c3018, c9494, c2175, c3770, c2532, c2551, c9547, c4088, c9584, c9332, c3213, c205, c3214, c2985, c3278, c3217] c9585 unsat9585 (by rfl) a
  have h0 : Entails.eval a c9577 := derived9577 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9580 := derived9580 a h
  have h3 : Entails.eval a c2999 := h 2998 (by decide)
  have h4 : Entails.eval a c3022 := h 3021 (by decide)
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9217 := derived9217 a h
  have h7 : Entails.eval a c3013 := h 3012 (by decide)
  have h8 : Entails.eval a c2425 := h 2424 (by decide)
  have h9 : Entails.eval a c2440 := h 2439 (by decide)
  have h10 : Entails.eval a c3018 := h 3017 (by decide)
  have h11 : Entails.eval a c9494 := derived9494 a h
  have h12 : Entails.eval a c2175 := h 2174 (by decide)
  have h13 : Entails.eval a c3770 := h 3769 (by decide)
  have h14 : Entails.eval a c2532 := h 2531 (by decide)
  have h15 : Entails.eval a c2551 := h 2550 (by decide)
  have h16 : Entails.eval a c9547 := derived9547 a h
  have h17 : Entails.eval a c4088 := h 4087 (by decide)
  have h18 : Entails.eval a c9584 := derived9584 a h
  have h19 : Entails.eval a c9332 := derived9332 a h
  have h20 : Entails.eval a c3213 := h 3212 (by decide)
  have h21 : Entails.eval a c205 := h 204 (by decide)
  have h22 : Entails.eval a c3214 := h 3213 (by decide)
  have h23 : Entails.eval a c2985 := h 2984 (by decide)
  have h24 : Entails.eval a c3278 := h 3277 (by decide)
  have h25 : Entails.eval a c3217 := h 3216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9586 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9586 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9583, some c2396, some c2996, some c2394, some c2988, some c2978, some c2389, some c2381, some c2379, some c2403, some c2413, some c2382, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9586 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9586 : lratChecker f9586 p9586 = .success := by decide +kernel
theorem unsat9586 : Unsatisfiable (PosFin 65) f9586 := by
  apply lratCheckerSound f9586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9586
  · intro a ha; simp [p9586] at ha; subst a; trivial
  · exact checked9586
theorem derived9586 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9586 := by
  apply localUnsat_implies_entails f9586 [c9583, c2396, c2996, c2394, c2988, c2978, c2389, c2381, c2379, c2403, c2413, c2382] c9586 unsat9586 (by rfl) a
  have h0 : Entails.eval a c9583 := derived9583 a h
  have h1 : Entails.eval a c2396 := h 2395 (by decide)
  have h2 : Entails.eval a c2996 := h 2995 (by decide)
  have h3 : Entails.eval a c2394 := h 2393 (by decide)
  have h4 : Entails.eval a c2988 := h 2987 (by decide)
  have h5 : Entails.eval a c2978 := h 2977 (by decide)
  have h6 : Entails.eval a c2389 := h 2388 (by decide)
  have h7 : Entails.eval a c2381 := h 2380 (by decide)
  have h8 : Entails.eval a c2379 := h 2378 (by decide)
  have h9 : Entails.eval a c2403 := h 2402 (by decide)
  have h10 : Entails.eval a c2413 := h 2412 (by decide)
  have h11 : Entails.eval a c2382 := h 2381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9587 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9587 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9583, some c9586, some c2401, some c2990, some c2974, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9587 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9587 : lratChecker f9587 p9587 = .success := by decide +kernel
theorem unsat9587 : Unsatisfiable (PosFin 65) f9587 := by
  apply lratCheckerSound f9587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9587
  · intro a ha; simp [p9587] at ha; subst a; trivial
  · exact checked9587
theorem derived9587 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9587 := by
  apply localUnsat_implies_entails f9587 [c9583, c9586, c2401, c2990, c2974] c9587 unsat9587 (by rfl) a
  have h0 : Entails.eval a c9583 := derived9583 a h
  have h1 : Entails.eval a c9586 := derived9586 a h
  have h2 : Entails.eval a c2401 := h 2400 (by decide)
  have h3 : Entails.eval a c2990 := h 2989 (by decide)
  have h4 : Entails.eval a c2974 := h 2973 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9588 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9588 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c9347, some c2159, some c2155, some c2392, some c2985, some c2968, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9588 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9588 : lratChecker f9588 p9588 = .success := by decide +kernel
theorem unsat9588 : Unsatisfiable (PosFin 65) f9588 := by
  apply lratCheckerSound f9588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9588
  · intro a ha; simp [p9588] at ha; subst a; trivial
  · exact checked9588
theorem derived9588 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9588 := by
  apply localUnsat_implies_entails f9588 [c9534, c9494, c9347, c2159, c2155, c2392, c2985, c2968] c9588 unsat9588 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2159 := h 2158 (by decide)
  have h4 : Entails.eval a c2155 := h 2154 (by decide)
  have h5 : Entails.eval a c2392 := h 2391 (by decide)
  have h6 : Entails.eval a c2985 := h 2984 (by decide)
  have h7 : Entails.eval a c2968 := h 2967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9589 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9589 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c2408, some c2160, some c2158, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9589 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9589 : lratChecker f9589 p9589 = .success := by decide +kernel
theorem unsat9589 : Unsatisfiable (PosFin 65) f9589 := by
  apply lratCheckerSound f9589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9589
  · intro a ha; simp [p9589] at ha; subst a; trivial
  · exact checked9589
theorem derived9589 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9589 := by
  apply localUnsat_implies_entails f9589 [c9347, c2408, c2160, c2158] c9589 unsat9589 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c2408 := h 2407 (by decide)
  have h2 : Entails.eval a c2160 := h 2159 (by decide)
  have h3 : Entails.eval a c2158 := h 2157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9590 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9590 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2989, some c2399, some c2973, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9590 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9590 : lratChecker f9590 p9590 = .success := by decide +kernel
theorem unsat9590 : Unsatisfiable (PosFin 65) f9590 := by
  apply lratCheckerSound f9590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9590
  · intro a ha; simp [p9590] at ha; subst a; trivial
  · exact checked9590
theorem derived9590 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9590 := by
  apply localUnsat_implies_entails f9590 [c2989, c2399, c2973] c9590 unsat9590 (by rfl) a
  have h0 : Entails.eval a c2989 := h 2988 (by decide)
  have h1 : Entails.eval a c2399 := h 2398 (by decide)
  have h2 : Entails.eval a c2973 := h 2972 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9591 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9591 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c9347, some c9588, some c9589, some c2392, some c2157, some c2539, some c5091, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9591 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9591 : lratChecker f9591 p9591 = .success := by decide +kernel
theorem unsat9591 : Unsatisfiable (PosFin 65) f9591 := by
  apply lratCheckerSound f9591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9591
  · intro a ha; simp [p9591] at ha; subst a; trivial
  · exact checked9591
theorem derived9591 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9591 := by
  apply localUnsat_implies_entails f9591 [c9534, c9494, c9347, c9588, c9589, c2392, c2157, c2539, c5091] c9591 unsat9591 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9588 := derived9588 a h
  have h4 : Entails.eval a c9589 := derived9589 a h
  have h5 : Entails.eval a c2392 := h 2391 (by decide)
  have h6 : Entails.eval a c2157 := h 2156 (by decide)
  have h7 : Entails.eval a c2539 := h 2538 (by decide)
  have h8 : Entails.eval a c5091 := h 5090 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9592 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9592 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2463, some c2454, some c2392, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9592 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9592 : lratChecker f9592 p9592 = .success := by decide +kernel
theorem unsat9592 : Unsatisfiable (PosFin 65) f9592 := by
  apply lratCheckerSound f9592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9592
  · intro a ha; simp [p9592] at ha; subst a; trivial
  · exact checked9592
theorem derived9592 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9592 := by
  apply localUnsat_implies_entails f9592 [c2463, c2454, c2392] c9592 unsat9592 (by rfl) a
  have h0 : Entails.eval a c2463 := h 2462 (by decide)
  have h1 : Entails.eval a c2454 := h 2453 (by decide)
  have h2 : Entails.eval a c2392 := h 2391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9593 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9593 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2466, some c2465, some c2461, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9593 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9593 : lratChecker f9593 p9593 = .success := by decide +kernel
theorem unsat9593 : Unsatisfiable (PosFin 65) f9593 := by
  apply lratCheckerSound f9593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9593
  · intro a ha; simp [p9593] at ha; subst a; trivial
  · exact checked9593
theorem derived9593 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9593 := by
  apply localUnsat_implies_entails f9593 [c2466, c2465, c2461] c9593 unsat9593 (by rfl) a
  have h0 : Entails.eval a c2466 := h 2465 (by decide)
  have h1 : Entails.eval a c2465 := h 2464 (by decide)
  have h2 : Entails.eval a c2461 := h 2460 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9594 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9594 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3013, some c2425, some c2440, some c3006, some c2444, some c9587, some c2392, some c9590, some c2968, some c2379, some c2391, some c2985, some c2395, some c2381, some c2380, some c2998, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9594 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked9594 : lratChecker f9594 p9594 = .success := by decide +kernel
theorem unsat9594 : Unsatisfiable (PosFin 65) f9594 := by
  apply lratCheckerSound f9594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9594
  · intro a ha; simp [p9594] at ha; subst a; trivial
  · exact checked9594
theorem derived9594 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9594 := by
  apply localUnsat_implies_entails f9594 [c3013, c2425, c2440, c3006, c2444, c9587, c2392, c9590, c2968, c2379, c2391, c2985, c2395, c2381, c2380, c2998] c9594 unsat9594 (by rfl) a
  have h0 : Entails.eval a c3013 := h 3012 (by decide)
  have h1 : Entails.eval a c2425 := h 2424 (by decide)
  have h2 : Entails.eval a c2440 := h 2439 (by decide)
  have h3 : Entails.eval a c3006 := h 3005 (by decide)
  have h4 : Entails.eval a c2444 := h 2443 (by decide)
  have h5 : Entails.eval a c9587 := derived9587 a h
  have h6 : Entails.eval a c2392 := h 2391 (by decide)
  have h7 : Entails.eval a c9590 := derived9590 a h
  have h8 : Entails.eval a c2968 := h 2967 (by decide)
  have h9 : Entails.eval a c2379 := h 2378 (by decide)
  have h10 : Entails.eval a c2391 := h 2390 (by decide)
  have h11 : Entails.eval a c2985 := h 2984 (by decide)
  have h12 : Entails.eval a c2395 := h 2394 (by decide)
  have h13 : Entails.eval a c2381 := h 2380 (by decide)
  have h14 : Entails.eval a c2380 := h 2379 (by decide)
  have h15 : Entails.eval a c2998 := h 2997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9595 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9595 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9347, some c9591, some c9592, some c9593, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9595 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9595 : lratChecker f9595 p9595 = .success := by decide +kernel
theorem unsat9595 : Unsatisfiable (PosFin 65) f9595 := by
  apply lratCheckerSound f9595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9595
  · intro a ha; simp [p9595] at ha; subst a; trivial
  · exact checked9595
theorem derived9595 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9595 := by
  apply localUnsat_implies_entails f9595 [c9534, c9347, c9591, c9592, c9593] c9595 unsat9595 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9591 := derived9591 a h
  have h3 : Entails.eval a c9592 := derived9592 a h
  have h4 : Entails.eval a c9593 := derived9593 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9596 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9596 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2974, some c2402, some c2991, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9596 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9596 : lratChecker f9596 p9596 = .success := by decide +kernel
theorem unsat9596 : Unsatisfiable (PosFin 65) f9596 := by
  apply lratCheckerSound f9596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9596
  · intro a ha; simp [p9596] at ha; subst a; trivial
  · exact checked9596
theorem derived9596 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9596 := by
  apply localUnsat_implies_entails f9596 [c2974, c2402, c2991] c9596 unsat9596 (by rfl) a
  have h0 : Entails.eval a c2974 := h 2973 (by decide)
  have h1 : Entails.eval a c2402 := h 2401 (by decide)
  have h2 : Entails.eval a c2991 := h 2990 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9597 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9597 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9577, some c9217, some c9347, some c9580, some c2999, some c3022, some c3013, some c2425, some c3006, some c2440, some c2444, some c9585, some c9587, some c9594, some c9595, some c9596, some c2981, some c2985, some c2968, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9597 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9597 : lratChecker f9597 p9597 = .success := by decide +kernel
theorem unsat9597 : Unsatisfiable (PosFin 65) f9597 := by
  apply lratCheckerSound f9597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9597
  · intro a ha; simp [p9597] at ha; subst a; trivial
  · exact checked9597
theorem derived9597 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9597 := by
  apply localUnsat_implies_entails f9597 [c9534, c9577, c9217, c9347, c9580, c2999, c3022, c3013, c2425, c3006, c2440, c2444, c9585, c9587, c9594, c9595, c9596, c2981, c2985, c2968] c9597 unsat9597 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9577 := derived9577 a h
  have h2 : Entails.eval a c9217 := derived9217 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9580 := derived9580 a h
  have h5 : Entails.eval a c2999 := h 2998 (by decide)
  have h6 : Entails.eval a c3022 := h 3021 (by decide)
  have h7 : Entails.eval a c3013 := h 3012 (by decide)
  have h8 : Entails.eval a c2425 := h 2424 (by decide)
  have h9 : Entails.eval a c3006 := h 3005 (by decide)
  have h10 : Entails.eval a c2440 := h 2439 (by decide)
  have h11 : Entails.eval a c2444 := h 2443 (by decide)
  have h12 : Entails.eval a c9585 := derived9585 a h
  have h13 : Entails.eval a c9587 := derived9587 a h
  have h14 : Entails.eval a c9594 := derived9594 a h
  have h15 : Entails.eval a c9595 := derived9595 a h
  have h16 : Entails.eval a c9596 := derived9596 a h
  have h17 : Entails.eval a c2981 := h 2980 (by decide)
  have h18 : Entails.eval a c2985 := h 2984 (by decide)
  have h19 : Entails.eval a c2968 := h 2967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9598 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9598 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9324, some c9527, some c3010, some c9228, some c4945, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9598 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9598 : lratChecker f9598 p9598 = .success := by decide +kernel
theorem unsat9598 : Unsatisfiable (PosFin 65) f9598 := by
  apply lratCheckerSound f9598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9598
  · intro a ha; simp [p9598] at ha; subst a; trivial
  · exact checked9598
theorem derived9598 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9598 := by
  apply localUnsat_implies_entails f9598 [c9324, c9527, c3010, c9228, c4945] c9598 unsat9598 (by rfl) a
  have h0 : Entails.eval a c9324 := derived9324 a h
  have h1 : Entails.eval a c9527 := derived9527 a h
  have h2 : Entails.eval a c3010 := h 3009 (by decide)
  have h3 : Entails.eval a c9228 := derived9228 a h
  have h4 : Entails.eval a c4945 := h 4944 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9599 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨57, by decide⟩, true), (⟨61, by decide⟩, true), (⟨11, by decide⟩, true), (⟨64, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9599 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c2849, some c2175, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9599 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9599 : lratChecker f9599 p9599 = .success := by decide +kernel
theorem unsat9599 : Unsatisfiable (PosFin 65) f9599 := by
  apply lratCheckerSound f9599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9599
  · intro a ha; simp [p9599] at ha; subst a; trivial
  · exact checked9599
theorem derived9599 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9599 := by
  apply localUnsat_implies_entails f9599 [c9347, c2849, c2175] c9599 unsat9599 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c2849 := h 2848 (by decide)
  have h2 : Entails.eval a c2175 := h 2174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9600 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9600 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9577, some c9217, some c9494, some c9347, some c9597, some c9598, some c2999, some c3022, some c3013, some c2425, some c3006, some c9594, some c2440, some c2444, some c9587, some c9599, some c9595, some c9596, some c2981, some c2985, some c2968, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9600 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9600 : lratChecker f9600 p9600 = .success := by decide +kernel
theorem unsat9600 : Unsatisfiable (PosFin 65) f9600 := by
  apply lratCheckerSound f9600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9600
  · intro a ha; simp [p9600] at ha; subst a; trivial
  · exact checked9600
theorem derived9600 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9600 := by
  apply localUnsat_implies_entails f9600 [c9534, c9577, c9217, c9494, c9347, c9597, c9598, c2999, c3022, c3013, c2425, c3006, c9594, c2440, c2444, c9587, c9599, c9595, c9596, c2981, c2985, c2968] c9600 unsat9600 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9577 := derived9577 a h
  have h2 : Entails.eval a c9217 := derived9217 a h
  have h3 : Entails.eval a c9494 := derived9494 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9597 := derived9597 a h
  have h6 : Entails.eval a c9598 := derived9598 a h
  have h7 : Entails.eval a c2999 := h 2998 (by decide)
  have h8 : Entails.eval a c3022 := h 3021 (by decide)
  have h9 : Entails.eval a c3013 := h 3012 (by decide)
  have h10 : Entails.eval a c2425 := h 2424 (by decide)
  have h11 : Entails.eval a c3006 := h 3005 (by decide)
  have h12 : Entails.eval a c9594 := derived9594 a h
  have h13 : Entails.eval a c2440 := h 2439 (by decide)
  have h14 : Entails.eval a c2444 := h 2443 (by decide)
  have h15 : Entails.eval a c9587 := derived9587 a h
  have h16 : Entails.eval a c9599 := derived9599 a h
  have h17 : Entails.eval a c9595 := derived9595 a h
  have h18 : Entails.eval a c9596 := derived9596 a h
  have h19 : Entails.eval a c2981 := h 2980 (by decide)
  have h20 : Entails.eval a c2985 := h 2984 (by decide)
  have h21 : Entails.eval a c2968 := h 2967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9601 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9601 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3013, some c3012, some c3008, some c2427, some c2441, some c2432, some c2445, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9601 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9601 : lratChecker f9601 p9601 = .success := by decide +kernel
theorem unsat9601 : Unsatisfiable (PosFin 65) f9601 := by
  apply lratCheckerSound f9601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9601
  · intro a ha; simp [p9601] at ha; subst a; trivial
  · exact checked9601
theorem derived9601 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9601 := by
  apply localUnsat_implies_entails f9601 [c3013, c3012, c3008, c2427, c2441, c2432, c2445] c9601 unsat9601 (by rfl) a
  have h0 : Entails.eval a c3013 := h 3012 (by decide)
  have h1 : Entails.eval a c3012 := h 3011 (by decide)
  have h2 : Entails.eval a c3008 := h 3007 (by decide)
  have h3 : Entails.eval a c2427 := h 2426 (by decide)
  have h4 : Entails.eval a c2441 := h 2440 (by decide)
  have h5 : Entails.eval a c2432 := h 2431 (by decide)
  have h6 : Entails.eval a c2445 := h 2444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9602 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨63, by decide⟩, false), (⟨15, by decide⟩, false), (⟨60, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9602 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c9347, some c2396, some c1055, some c2996, some c727, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9602 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9602 : lratChecker f9602 p9602 = .success := by decide +kernel
theorem unsat9602 : Unsatisfiable (PosFin 65) f9602 := by
  apply lratCheckerSound f9602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9602
  · intro a ha; simp [p9602] at ha; subst a; trivial
  · exact checked9602
theorem derived9602 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9602 := by
  apply localUnsat_implies_entails f9602 [c9534, c9494, c9347, c2396, c1055, c2996, c727] c9602 unsat9602 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2396 := h 2395 (by decide)
  have h4 : Entails.eval a c1055 := h 1054 (by decide)
  have h5 : Entails.eval a c2996 := h 2995 (by decide)
  have h6 : Entails.eval a c727 := h 726 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9603 : DefaultClause 65 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9603 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9577, some c9534, some c9347, some c9217, some c9601, some c3022, some c3004, some c3010, some c3016, some c3012, some c2427, some c2445, some c3008, some c9535, some c9600, some c9583, some c9602, some c2401, some c2990, some c2975, some c2976, some c8713, some c6009, some c8863, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9603 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9603 : lratChecker f9603 p9603 = .success := by decide +kernel
theorem unsat9603 : Unsatisfiable (PosFin 65) f9603 := by
  apply lratCheckerSound f9603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9603
  · intro a ha; simp [p9603] at ha; subst a; trivial
  · exact checked9603
theorem derived9603 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9603 := by
  apply localUnsat_implies_entails f9603 [c9577, c9534, c9347, c9217, c9601, c3022, c3004, c3010, c3016, c3012, c2427, c2445, c3008, c9535, c9600, c9583, c9602, c2401, c2990, c2975, c2976, c8713, c6009, c8863] c9603 unsat9603 (by rfl) a
  have h0 : Entails.eval a c9577 := derived9577 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9217 := derived9217 a h
  have h4 : Entails.eval a c9601 := derived9601 a h
  have h5 : Entails.eval a c3022 := h 3021 (by decide)
  have h6 : Entails.eval a c3004 := h 3003 (by decide)
  have h7 : Entails.eval a c3010 := h 3009 (by decide)
  have h8 : Entails.eval a c3016 := h 3015 (by decide)
  have h9 : Entails.eval a c3012 := h 3011 (by decide)
  have h10 : Entails.eval a c2427 := h 2426 (by decide)
  have h11 : Entails.eval a c2445 := h 2444 (by decide)
  have h12 : Entails.eval a c3008 := h 3007 (by decide)
  have h13 : Entails.eval a c9535 := derived9535 a h
  have h14 : Entails.eval a c9600 := derived9600 a h
  have h15 : Entails.eval a c9583 := derived9583 a h
  have h16 : Entails.eval a c9602 := derived9602 a h
  have h17 : Entails.eval a c2401 := h 2400 (by decide)
  have h18 : Entails.eval a c2990 := h 2989 (by decide)
  have h19 : Entails.eval a c2975 := h 2974 (by decide)
  have h20 : Entails.eval a c2976 := h 2975 (by decide)
  have h21 : Entails.eval a c8713 := derived8713 a h
  have h22 : Entails.eval a c6009 := h 6008 (by decide)
  have h23 : Entails.eval a c8863 := derived8863 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9604 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨63, by decide⟩, false), (⟨59, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9604 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3016, some c3008, some c3012, some c2970, some c2384, some c2977, some c9542, some c5354, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9604 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9604 : lratChecker f9604 p9604 = .success := by decide +kernel
theorem unsat9604 : Unsatisfiable (PosFin 65) f9604 := by
  apply lratCheckerSound f9604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9604
  · intro a ha; simp [p9604] at ha; subst a; trivial
  · exact checked9604
theorem derived9604 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9604 := by
  apply localUnsat_implies_entails f9604 [c3016, c3008, c3012, c2970, c2384, c2977, c9542, c5354] c9604 unsat9604 (by rfl) a
  have h0 : Entails.eval a c3016 := h 3015 (by decide)
  have h1 : Entails.eval a c3008 := h 3007 (by decide)
  have h2 : Entails.eval a c3012 := h 3011 (by decide)
  have h3 : Entails.eval a c2970 := h 2969 (by decide)
  have h4 : Entails.eval a c2384 := h 2383 (by decide)
  have h5 : Entails.eval a c2977 := h 2976 (by decide)
  have h6 : Entails.eval a c9542 := derived9542 a h
  have h7 : Entails.eval a c5354 := h 5353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9605 : DefaultClause 65 := directClause [(⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨64, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9605 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9217, some c9601, some c3022, some c3004, some c3010, some c3016, some c3012, some c2427, some c2445, some c9604, some c3008, some c9538, some c9542, some c3215, some c3279, some c2379, some c2381, some c8897, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9605 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9605 : lratChecker f9605 p9605 = .success := by decide +kernel
theorem unsat9605 : Unsatisfiable (PosFin 65) f9605 := by
  apply lratCheckerSound f9605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9605
  · intro a ha; simp [p9605] at ha; subst a; trivial
  · exact checked9605
theorem derived9605 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9605 := by
  apply localUnsat_implies_entails f9605 [c9217, c9601, c3022, c3004, c3010, c3016, c3012, c2427, c2445, c9604, c3008, c9538, c9542, c3215, c3279, c2379, c2381, c8897] c9605 unsat9605 (by rfl) a
  have h0 : Entails.eval a c9217 := derived9217 a h
  have h1 : Entails.eval a c9601 := derived9601 a h
  have h2 : Entails.eval a c3022 := h 3021 (by decide)
  have h3 : Entails.eval a c3004 := h 3003 (by decide)
  have h4 : Entails.eval a c3010 := h 3009 (by decide)
  have h5 : Entails.eval a c3016 := h 3015 (by decide)
  have h6 : Entails.eval a c3012 := h 3011 (by decide)
  have h7 : Entails.eval a c2427 := h 2426 (by decide)
  have h8 : Entails.eval a c2445 := h 2444 (by decide)
  have h9 : Entails.eval a c9604 := derived9604 a h
  have h10 : Entails.eval a c3008 := h 3007 (by decide)
  have h11 : Entails.eval a c9538 := derived9538 a h
  have h12 : Entails.eval a c9542 := derived9542 a h
  have h13 : Entails.eval a c3215 := h 3214 (by decide)
  have h14 : Entails.eval a c3279 := h 3278 (by decide)
  have h15 : Entails.eval a c2379 := h 2378 (by decide)
  have h16 : Entails.eval a c2381 := h 2380 (by decide)
  have h17 : Entails.eval a c8897 := derived8897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9606 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false), (⟨62, by decide⟩, false), (⟨59, by decide⟩, false), (⟨15, by decide⟩, false), (⟨60, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9606 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3004, some c2427, some c2445, some c2530, some c2545, some c4090, some c5116, some c9239, some c3215, some c3279, some c3274, some c2379, some c2990, some c2381, some c6082, some c989, some c1052, some c2413, some c2504, some c2450, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨62, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9606 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9606 : lratChecker f9606 p9606 = .success := by decide +kernel
theorem unsat9606 : Unsatisfiable (PosFin 65) f9606 := by
  apply lratCheckerSound f9606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9606
  · intro a ha; simp [p9606] at ha; subst a; trivial
  · exact checked9606
theorem derived9606 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9606 := by
  apply localUnsat_implies_entails f9606 [c3004, c2427, c2445, c2530, c2545, c4090, c5116, c9239, c3215, c3279, c3274, c2379, c2990, c2381, c6082, c989, c1052, c2413, c2504, c2450] c9606 unsat9606 (by rfl) a
  have h0 : Entails.eval a c3004 := h 3003 (by decide)
  have h1 : Entails.eval a c2427 := h 2426 (by decide)
  have h2 : Entails.eval a c2445 := h 2444 (by decide)
  have h3 : Entails.eval a c2530 := h 2529 (by decide)
  have h4 : Entails.eval a c2545 := h 2544 (by decide)
  have h5 : Entails.eval a c4090 := h 4089 (by decide)
  have h6 : Entails.eval a c5116 := h 5115 (by decide)
  have h7 : Entails.eval a c9239 := derived9239 a h
  have h8 : Entails.eval a c3215 := h 3214 (by decide)
  have h9 : Entails.eval a c3279 := h 3278 (by decide)
  have h10 : Entails.eval a c3274 := h 3273 (by decide)
  have h11 : Entails.eval a c2379 := h 2378 (by decide)
  have h12 : Entails.eval a c2990 := h 2989 (by decide)
  have h13 : Entails.eval a c2381 := h 2380 (by decide)
  have h14 : Entails.eval a c6082 := h 6081 (by decide)
  have h15 : Entails.eval a c989 := h 988 (by decide)
  have h16 : Entails.eval a c1052 := h 1051 (by decide)
  have h17 : Entails.eval a c2413 := h 2412 (by decide)
  have h18 : Entails.eval a c2504 := h 2503 (by decide)
  have h19 : Entails.eval a c2450 := h 2449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9607 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9607 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9600, some c9534, some c9577, some c9217, some c9494, some c9347, some c9601, some c3022, some c3004, some c9535, some c3010, some c3016, some c3012, some c3008, some c2427, some c2445, some c9536, some c9603, some c9604, some c9605, some c2530, some c2545, some c5125, some c4090, some c9606, some c4912, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9607 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9607 : lratChecker f9607 p9607 = .success := by decide +kernel
theorem unsat9607 : Unsatisfiable (PosFin 65) f9607 := by
  apply lratCheckerSound f9607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9607
  · intro a ha; simp [p9607] at ha; subst a; trivial
  · exact checked9607
theorem derived9607 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9607 := by
  apply localUnsat_implies_entails f9607 [c9600, c9534, c9577, c9217, c9494, c9347, c9601, c3022, c3004, c9535, c3010, c3016, c3012, c3008, c2427, c2445, c9536, c9603, c9604, c9605, c2530, c2545, c5125, c4090, c9606, c4912] c9607 unsat9607 (by rfl) a
  have h0 : Entails.eval a c9600 := derived9600 a h
  have h1 : Entails.eval a c9534 := derived9534 a h
  have h2 : Entails.eval a c9577 := derived9577 a h
  have h3 : Entails.eval a c9217 := derived9217 a h
  have h4 : Entails.eval a c9494 := derived9494 a h
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9601 := derived9601 a h
  have h7 : Entails.eval a c3022 := h 3021 (by decide)
  have h8 : Entails.eval a c3004 := h 3003 (by decide)
  have h9 : Entails.eval a c9535 := derived9535 a h
  have h10 : Entails.eval a c3010 := h 3009 (by decide)
  have h11 : Entails.eval a c3016 := h 3015 (by decide)
  have h12 : Entails.eval a c3012 := h 3011 (by decide)
  have h13 : Entails.eval a c3008 := h 3007 (by decide)
  have h14 : Entails.eval a c2427 := h 2426 (by decide)
  have h15 : Entails.eval a c2445 := h 2444 (by decide)
  have h16 : Entails.eval a c9536 := derived9536 a h
  have h17 : Entails.eval a c9603 := derived9603 a h
  have h18 : Entails.eval a c9604 := derived9604 a h
  have h19 : Entails.eval a c9605 := derived9605 a h
  have h20 : Entails.eval a c2530 := h 2529 (by decide)
  have h21 : Entails.eval a c2545 := h 2544 (by decide)
  have h22 : Entails.eval a c5125 := h 5124 (by decide)
  have h23 : Entails.eval a c4090 := h 4089 (by decide)
  have h24 : Entails.eval a c9606 := derived9606 a h
  have h25 : Entails.eval a c4912 := h 4911 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9608 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9608 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9534, some c9494, some c9347, some c9577, some c9217, some c9600, some c9607, some c2999, some c3022, some c2425, some c3006, some c2480, some c2176, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9608 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9608 : lratChecker f9608 p9608 = .success := by decide +kernel
theorem unsat9608 : Unsatisfiable (PosFin 65) f9608 := by
  apply lratCheckerSound f9608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9608
  · intro a ha; simp [p9608] at ha; subst a; trivial
  · exact checked9608
theorem derived9608 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9608 := by
  apply localUnsat_implies_entails f9608 [c9534, c9494, c9347, c9577, c9217, c9600, c9607, c2999, c3022, c2425, c3006, c2480, c2176] c9608 unsat9608 (by rfl) a
  have h0 : Entails.eval a c9534 := derived9534 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9577 := derived9577 a h
  have h4 : Entails.eval a c9217 := derived9217 a h
  have h5 : Entails.eval a c9600 := derived9600 a h
  have h6 : Entails.eval a c9607 := derived9607 a h
  have h7 : Entails.eval a c2999 := h 2998 (by decide)
  have h8 : Entails.eval a c3022 := h 3021 (by decide)
  have h9 : Entails.eval a c2425 := h 2424 (by decide)
  have h10 : Entails.eval a c3006 := h 3005 (by decide)
  have h11 : Entails.eval a c2480 := h 2479 (by decide)
  have h12 : Entails.eval a c2176 := h 2175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9609 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9609 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9347, some c9534, some c9608, some c7994, some c8269, some c9533, some c3009, some c2445, some c2444, some c2420, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9609 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9609 : lratChecker f9609 p9609 = .success := by decide +kernel
theorem unsat9609 : Unsatisfiable (PosFin 65) f9609 := by
  apply lratCheckerSound f9609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9609
  · intro a ha; simp [p9609] at ha; subst a; trivial
  · exact checked9609
theorem derived9609 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9609 := by
  apply localUnsat_implies_entails f9609 [c9494, c9347, c9534, c9608, c7994, c8269, c9533, c3009, c2445, c2444, c2420] c9609 unsat9609 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9534 := derived9534 a h
  have h3 : Entails.eval a c9608 := derived9608 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c9533 := derived9533 a h
  have h7 : Entails.eval a c3009 := h 3008 (by decide)
  have h8 : Entails.eval a c2445 := h 2444 (by decide)
  have h9 : Entails.eval a c2444 := h 2443 (by decide)
  have h10 : Entails.eval a c2420 := h 2419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9610 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9610 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9533, some c9609, some c9347, some c1292, some c3419, some c3433, some c1281, some c2912, some c4856, some c4946, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9610 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9610 : lratChecker f9610 p9610 = .success := by decide +kernel
theorem unsat9610 : Unsatisfiable (PosFin 65) f9610 := by
  apply lratCheckerSound f9610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9610
  · intro a ha; simp [p9610] at ha; subst a; trivial
  · exact checked9610
theorem derived9610 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9610 := by
  apply localUnsat_implies_entails f9610 [c9494, c9533, c9609, c9347, c1292, c3419, c3433, c1281, c2912, c4856, c4946] c9610 unsat9610 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9533 := derived9533 a h
  have h2 : Entails.eval a c9609 := derived9609 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c1292 := h 1291 (by decide)
  have h5 : Entails.eval a c3419 := h 3418 (by decide)
  have h6 : Entails.eval a c3433 := h 3432 (by decide)
  have h7 : Entails.eval a c1281 := h 1280 (by decide)
  have h8 : Entails.eval a c2912 := h 2911 (by decide)
  have h9 : Entails.eval a c4856 := h 4855 (by decide)
  have h10 : Entails.eval a c4946 := h 4945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9611 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9611 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9533, some c9498, some c9609, some c9347, some c1272, some c1285, some c1286, some c1303, some c3421, some c1288, some c2881, some c8388, some c9484, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9611 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9611 : lratChecker f9611 p9611 = .success := by decide +kernel
theorem unsat9611 : Unsatisfiable (PosFin 65) f9611 := by
  apply lratCheckerSound f9611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9611
  · intro a ha; simp [p9611] at ha; subst a; trivial
  · exact checked9611
theorem derived9611 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9611 := by
  apply localUnsat_implies_entails f9611 [c9494, c9533, c9498, c9609, c9347, c1272, c1285, c1286, c1303, c3421, c1288, c2881, c8388, c9484] c9611 unsat9611 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9533 := derived9533 a h
  have h2 : Entails.eval a c9498 := derived9498 a h
  have h3 : Entails.eval a c9609 := derived9609 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c1272 := h 1271 (by decide)
  have h6 : Entails.eval a c1285 := h 1284 (by decide)
  have h7 : Entails.eval a c1286 := h 1285 (by decide)
  have h8 : Entails.eval a c1303 := h 1302 (by decide)
  have h9 : Entails.eval a c3421 := h 3420 (by decide)
  have h10 : Entails.eval a c1288 := h 1287 (by decide)
  have h11 : Entails.eval a c2881 := h 2880 (by decide)
  have h12 : Entails.eval a c8388 := derived8388 a h
  have h13 : Entails.eval a c9484 := derived9484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9612 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9612 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3420, some c2879, some c2913, some c3808, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9612 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9612 : lratChecker f9612 p9612 = .success := by decide +kernel
theorem unsat9612 : Unsatisfiable (PosFin 65) f9612 := by
  apply lratCheckerSound f9612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9612
  · intro a ha; simp [p9612] at ha; subst a; trivial
  · exact checked9612
theorem derived9612 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9612 := by
  apply localUnsat_implies_entails f9612 [c3420, c2879, c2913, c3808] c9612 unsat9612 (by rfl) a
  have h0 : Entails.eval a c3420 := h 3419 (by decide)
  have h1 : Entails.eval a c2879 := h 2878 (by decide)
  have h2 : Entails.eval a c2913 := h 2912 (by decide)
  have h3 : Entails.eval a c3808 := h 3807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9613 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9613 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9494, some c9533, some c9609, some c9347, some c9498, some c9612, some c1272, some c1271, some c9611, some c1283, some c9610, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9613 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9613 : lratChecker f9613 p9613 = .success := by decide +kernel
theorem unsat9613 : Unsatisfiable (PosFin 65) f9613 := by
  apply lratCheckerSound f9613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9613
  · intro a ha; simp [p9613] at ha; subst a; trivial
  · exact checked9613
theorem derived9613 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9613 := by
  apply localUnsat_implies_entails f9613 [c9494, c9533, c9609, c9347, c9498, c9612, c1272, c1271, c9611, c1283, c9610] c9613 unsat9613 (by rfl) a
  have h0 : Entails.eval a c9494 := derived9494 a h
  have h1 : Entails.eval a c9533 := derived9533 a h
  have h2 : Entails.eval a c9609 := derived9609 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9498 := derived9498 a h
  have h5 : Entails.eval a c9612 := derived9612 a h
  have h6 : Entails.eval a c1272 := h 1271 (by decide)
  have h7 : Entails.eval a c1271 := h 1270 (by decide)
  have h8 : Entails.eval a c9611 := derived9611 a h
  have h9 : Entails.eval a c1283 := h 1282 (by decide)
  have h10 : Entails.eval a c9610 := derived9610 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9614 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9614 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3434, some c3766, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9614 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9614 : lratChecker f9614 p9614 = .success := by decide +kernel
theorem unsat9614 : Unsatisfiable (PosFin 65) f9614 := by
  apply lratCheckerSound f9614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9614
  · intro a ha; simp [p9614] at ha; subst a; trivial
  · exact checked9614
theorem derived9614 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9614 := by
  apply localUnsat_implies_entails f9614 [c3434, c3766] c9614 unsat9614 (by rfl) a
  have h0 : Entails.eval a c3434 := h 3433 (by decide)
  have h1 : Entails.eval a c3766 := h 3765 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9615 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨4, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9615 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3435, some c3767, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9615 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9615 : lratChecker f9615 p9615 = .success := by decide +kernel
theorem unsat9615 : Unsatisfiable (PosFin 65) f9615 := by
  apply lratCheckerSound f9615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9615
  · intro a ha; simp [p9615] at ha; subst a; trivial
  · exact checked9615
theorem derived9615 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9615 := by
  apply localUnsat_implies_entails f9615 [c3435, c3767] c9615 unsat9615 (by rfl) a
  have h0 : Entails.eval a c3435 := h 3434 (by decide)
  have h1 : Entails.eval a c3767 := h 3766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9616 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9616 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9609, some c9494, some c9533, some c9613, some c9614, some c9615, some c1286, some c1297, some c1292, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9616 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9616 : lratChecker f9616 p9616 = .success := by decide +kernel
theorem unsat9616 : Unsatisfiable (PosFin 65) f9616 := by
  apply lratCheckerSound f9616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9616
  · intro a ha; simp [p9616] at ha; subst a; trivial
  · exact checked9616
theorem derived9616 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9616 := by
  apply localUnsat_implies_entails f9616 [c9609, c9494, c9533, c9613, c9614, c9615, c1286, c1297, c1292] c9616 unsat9616 (by rfl) a
  have h0 : Entails.eval a c9609 := derived9609 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9533 := derived9533 a h
  have h3 : Entails.eval a c9613 := derived9613 a h
  have h4 : Entails.eval a c9614 := derived9614 a h
  have h5 : Entails.eval a c9615 := derived9615 a h
  have h6 : Entails.eval a c1286 := h 1285 (by decide)
  have h7 : Entails.eval a c1297 := h 1296 (by decide)
  have h8 : Entails.eval a c1292 := h 1291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9617 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9617 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9304, some c4948, some c4960, some c4949, some c4957, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9617 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9617 : lratChecker f9617 p9617 = .success := by decide +kernel
theorem unsat9617 : Unsatisfiable (PosFin 65) f9617 := by
  apply lratCheckerSound f9617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9617
  · intro a ha; simp [p9617] at ha; subst a; trivial
  · exact checked9617
theorem derived9617 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9617 := by
  apply localUnsat_implies_entails f9617 [c9304, c4948, c4960, c4949, c4957] c9617 unsat9617 (by rfl) a
  have h0 : Entails.eval a c9304 := derived9304 a h
  have h1 : Entails.eval a c4948 := h 4947 (by decide)
  have h2 : Entails.eval a c4960 := h 4959 (by decide)
  have h3 : Entails.eval a c4949 := h 4948 (by decide)
  have h4 : Entails.eval a c4957 := h 4956 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9618 : DefaultClause 65 := directClause [(⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9618 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9494, some c9347, some c9617, some c1385, some c2490, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9618 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9618 : lratChecker f9618 p9618 = .success := by decide +kernel
theorem unsat9618 : Unsatisfiable (PosFin 65) f9618 := by
  apply lratCheckerSound f9618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9618
  · intro a ha; simp [p9618] at ha; subst a; trivial
  · exact checked9618
theorem derived9618 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9618 := by
  apply localUnsat_implies_entails f9618 [c9616, c9609, c9494, c9347, c9617, c1385, c2490] c9618 unsat9618 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9617 := derived9617 a h
  have h5 : Entails.eval a c1385 := h 1384 (by decide)
  have h6 : Entails.eval a c2490 := h 2489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9619 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9619 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9494, some c9304, some c4948, some c4962, some c9478, some c8409, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9619 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9619 : lratChecker f9619 p9619 = .success := by decide +kernel
theorem unsat9619 : Unsatisfiable (PosFin 65) f9619 := by
  apply lratCheckerSound f9619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9619
  · intro a ha; simp [p9619] at ha; subst a; trivial
  · exact checked9619
theorem derived9619 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9619 := by
  apply localUnsat_implies_entails f9619 [c9616, c9609, c9494, c9304, c4948, c4962, c9478, c8409] c9619 unsat9619 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9304 := derived9304 a h
  have h4 : Entails.eval a c4948 := h 4947 (by decide)
  have h5 : Entails.eval a c4962 := h 4961 (by decide)
  have h6 : Entails.eval a c9478 := derived9478 a h
  have h7 : Entails.eval a c8409 := derived8409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9620 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨54, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9620 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2515, some c4961, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9620 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9620 : lratChecker f9620 p9620 = .success := by decide +kernel
theorem unsat9620 : Unsatisfiable (PosFin 65) f9620 := by
  apply lratCheckerSound f9620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9620
  · intro a ha; simp [p9620] at ha; subst a; trivial
  · exact checked9620
theorem derived9620 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9620 := by
  apply localUnsat_implies_entails f9620 [c2515, c4961] c9620 unsat9620 (by rfl) a
  have h0 : Entails.eval a c2515 := h 2514 (by decide)
  have h1 : Entails.eval a c4961 := h 4960 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9621 : DefaultClause 65 := directClause [(⟨55, by decide⟩, true), (⟨57, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9621 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9293, some c9294, some c9347, some c9619, some c8409, some c2475, some c2496, some c2502, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9621 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9621 : lratChecker f9621 p9621 = .success := by decide +kernel
theorem unsat9621 : Unsatisfiable (PosFin 65) f9621 := by
  apply lratCheckerSound f9621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9621
  · intro a ha; simp [p9621] at ha; subst a; trivial
  · exact checked9621
theorem derived9621 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9621 := by
  apply localUnsat_implies_entails f9621 [c9616, c9609, c9293, c9294, c9347, c9619, c8409, c2475, c2496, c2502] c9621 unsat9621 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9293 := derived9293 a h
  have h3 : Entails.eval a c9294 := derived9294 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9619 := derived9619 a h
  have h6 : Entails.eval a c8409 := derived8409 a h
  have h7 : Entails.eval a c2475 := h 2474 (by decide)
  have h8 : Entails.eval a c2496 := h 2495 (by decide)
  have h9 : Entails.eval a c2502 := h 2501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9622 : DefaultClause 65 := directClause [(⟨63, by decide⟩, true), (⟨52, by decide⟩, true), (⟨57, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9622 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9494, some c9347, some c2176, some c2481, some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9622 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9622 : lratChecker f9622 p9622 = .success := by decide +kernel
theorem unsat9622 : Unsatisfiable (PosFin 65) f9622 := by
  apply lratCheckerSound f9622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9622
  · intro a ha; simp [p9622] at ha; subst a; trivial
  · exact checked9622
theorem derived9622 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9622 := by
  apply localUnsat_implies_entails f9622 [c9616, c9494, c9347, c2176, c2481] c9622 unsat9622 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2176 := h 2175 (by decide)
  have h4 : Entails.eval a c2481 := h 2480 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9623 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9623 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9293, some c9294, some c9494, some c9347, some c9620, some c9621, some c9618, some c9622, some c1385, some c2490, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9623 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9623 : lratChecker f9623 p9623 = .success := by decide +kernel
theorem unsat9623 : Unsatisfiable (PosFin 65) f9623 := by
  apply lratCheckerSound f9623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9623
  · intro a ha; simp [p9623] at ha; subst a; trivial
  · exact checked9623
theorem derived9623 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9623 := by
  apply localUnsat_implies_entails f9623 [c9616, c9609, c9293, c9294, c9494, c9347, c9620, c9621, c9618, c9622, c1385, c2490] c9623 unsat9623 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9293 := derived9293 a h
  have h3 : Entails.eval a c9294 := derived9294 a h
  have h4 : Entails.eval a c9494 := derived9494 a h
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9620 := derived9620 a h
  have h7 : Entails.eval a c9621 := derived9621 a h
  have h8 : Entails.eval a c9618 := derived9618 a h
  have h9 : Entails.eval a c9622 := derived9622 a h
  have h10 : Entails.eval a c1385 := h 1384 (by decide)
  have h11 : Entails.eval a c2490 := h 2489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9624 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9624 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9293, some c9294, some c3331, some c3636, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p9624 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9624 : lratChecker f9624 p9624 = .success := by decide +kernel
theorem unsat9624 : Unsatisfiable (PosFin 65) f9624 := by
  apply lratCheckerSound f9624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9624
  · intro a ha; simp [p9624] at ha; subst a; trivial
  · exact checked9624
theorem derived9624 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9624 := by
  apply localUnsat_implies_entails f9624 [c9293, c9294, c3331, c3636] c9624 unsat9624 (by rfl) a
  have h0 : Entails.eval a c9293 := derived9293 a h
  have h1 : Entails.eval a c9294 := derived9294 a h
  have h2 : Entails.eval a c3331 := h 3330 (by decide)
  have h3 : Entails.eval a c3636 := h 3635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9625 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9625 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9494, some c9347, some c9293, some c9294, some c9624, some c9620, some c9623, some c9621, some c9305, some c4964, some c3644, some c3640, some c4958, some c9478, some c1372, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9625 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9625 : lratChecker f9625 p9625 = .success := by decide +kernel
theorem unsat9625 : Unsatisfiable (PosFin 65) f9625 := by
  apply lratCheckerSound f9625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9625
  · intro a ha; simp [p9625] at ha; subst a; trivial
  · exact checked9625
theorem derived9625 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9625 := by
  apply localUnsat_implies_entails f9625 [c9616, c9609, c9494, c9347, c9293, c9294, c9624, c9620, c9623, c9621, c9305, c4964, c3644, c3640, c4958, c9478, c1372] c9625 unsat9625 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9494 := derived9494 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9293 := derived9293 a h
  have h5 : Entails.eval a c9294 := derived9294 a h
  have h6 : Entails.eval a c9624 := derived9624 a h
  have h7 : Entails.eval a c9620 := derived9620 a h
  have h8 : Entails.eval a c9623 := derived9623 a h
  have h9 : Entails.eval a c9621 := derived9621 a h
  have h10 : Entails.eval a c9305 := derived9305 a h
  have h11 : Entails.eval a c4964 := h 4963 (by decide)
  have h12 : Entails.eval a c3644 := h 3643 (by decide)
  have h13 : Entails.eval a c3640 := h 3639 (by decide)
  have h14 : Entails.eval a c4958 := h 4957 (by decide)
  have h15 : Entails.eval a c9478 := derived9478 a h
  have h16 : Entails.eval a c1372 := h 1371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9626 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9626 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9616, some c9609, some c9347, some c9625, some c2423, some c2417, some c2419, some c3013, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9626 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9626 : lratChecker f9626 p9626 = .success := by decide +kernel
theorem unsat9626 : Unsatisfiable (PosFin 65) f9626 := by
  apply lratCheckerSound f9626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9626
  · intro a ha; simp [p9626] at ha; subst a; trivial
  · exact checked9626
theorem derived9626 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9626 := by
  apply localUnsat_implies_entails f9626 [c9616, c9609, c9347, c9625, c2423, c2417, c2419, c3013] c9626 unsat9626 (by rfl) a
  have h0 : Entails.eval a c9616 := derived9616 a h
  have h1 : Entails.eval a c9609 := derived9609 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9625 := derived9625 a h
  have h4 : Entails.eval a c2423 := h 2422 (by decide)
  have h5 : Entails.eval a c2417 := h 2416 (by decide)
  have h6 : Entails.eval a c2419 := h 2418 (by decide)
  have h7 : Entails.eval a c3013 := h 3012 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9627 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9627 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9494, some c9609, some c9616, some c9626, some c7994, some c8269, some c8383, some c9622, some c2166, some c2483, some c8018, some c2473, some c2501, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9627 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9627 : lratChecker f9627 p9627 = .success := by decide +kernel
theorem unsat9627 : Unsatisfiable (PosFin 65) f9627 := by
  apply lratCheckerSound f9627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9627
  · intro a ha; simp [p9627] at ha; subst a; trivial
  · exact checked9627
theorem derived9627 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9627 := by
  apply localUnsat_implies_entails f9627 [c9347, c9494, c9609, c9616, c9626, c7994, c8269, c8383, c9622, c2166, c2483, c8018, c2473, c2501] c9627 unsat9627 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9494 := derived9494 a h
  have h2 : Entails.eval a c9609 := derived9609 a h
  have h3 : Entails.eval a c9616 := derived9616 a h
  have h4 : Entails.eval a c9626 := derived9626 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c8269 := derived8269 a h
  have h7 : Entails.eval a c8383 := derived8383 a h
  have h8 : Entails.eval a c9622 := derived9622 a h
  have h9 : Entails.eval a c2166 := h 2165 (by decide)
  have h10 : Entails.eval a c2483 := h 2482 (by decide)
  have h11 : Entails.eval a c8018 := derived8018 a h
  have h12 : Entails.eval a c2473 := h 2472 (by decide)
  have h13 : Entails.eval a c2501 := h 2500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9628 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9628 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3166, some c2889, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9628 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9628 : lratChecker f9628 p9628 = .success := by decide +kernel
theorem unsat9628 : Unsatisfiable (PosFin 65) f9628 := by
  apply lratCheckerSound f9628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9628
  · intro a ha; simp [p9628] at ha; subst a; trivial
  · exact checked9628
theorem derived9628 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9628 := by
  apply localUnsat_implies_entails f9628 [c3166, c2889] c9628 unsat9628 (by rfl) a
  have h0 : Entails.eval a c3166 := h 3165 (by decide)
  have h1 : Entails.eval a c2889 := h 2888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9629 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9629 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9103, some c9628, some c3146, some c2876, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9629 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9629 : lratChecker f9629 p9629 = .success := by decide +kernel
theorem unsat9629 : Unsatisfiable (PosFin 65) f9629 := by
  apply lratCheckerSound f9629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9629
  · intro a ha; simp [p9629] at ha; subst a; trivial
  · exact checked9629
theorem derived9629 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9629 := by
  apply localUnsat_implies_entails f9629 [c9103, c9628, c3146, c2876] c9629 unsat9629 (by rfl) a
  have h0 : Entails.eval a c9103 := derived9103 a h
  have h1 : Entails.eval a c9628 := derived9628 a h
  have h2 : Entails.eval a c3146 := h 3145 (by decide)
  have h3 : Entails.eval a c2876 := h 2875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9630 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9630 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9129, some c9629, some c8420, some c9356, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9630 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9630 : lratChecker f9630 p9630 = .success := by decide +kernel
theorem unsat9630 : Unsatisfiable (PosFin 65) f9630 := by
  apply lratCheckerSound f9630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9630
  · intro a ha; simp [p9630] at ha; subst a; trivial
  · exact checked9630
theorem derived9630 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9630 := by
  apply localUnsat_implies_entails f9630 [c9347, c9129, c9629, c8420, c9356] c9630 unsat9630 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9129 := derived9129 a h
  have h2 : Entails.eval a c9629 := derived9629 a h
  have h3 : Entails.eval a c8420 := derived8420 a h
  have h4 : Entails.eval a c9356 := derived9356 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9631 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9631 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2113, some c1370, some c1359, some c1375, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9631 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9631 : lratChecker f9631 p9631 = .success := by decide +kernel
theorem unsat9631 : Unsatisfiable (PosFin 65) f9631 := by
  apply lratCheckerSound f9631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9631
  · intro a ha; simp [p9631] at ha; subst a; trivial
  · exact checked9631
theorem derived9631 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9631 := by
  apply localUnsat_implies_entails f9631 [c9627, c2113, c1370, c1359, c1375] c9631 unsat9631 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2113 := h 2112 (by decide)
  have h2 : Entails.eval a c1370 := h 1369 (by decide)
  have h3 : Entails.eval a c1359 := h 1358 (by decide)
  have h4 : Entails.eval a c1375 := h 1374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9632 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9632 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9478, some c2861, some c8007, some c4461, some c3875, some c2597, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9632 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9632 : lratChecker f9632 p9632 = .success := by decide +kernel
theorem unsat9632 : Unsatisfiable (PosFin 65) f9632 := by
  apply lratCheckerSound f9632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9632
  · intro a ha; simp [p9632] at ha; subst a; trivial
  · exact checked9632
theorem derived9632 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9632 := by
  apply localUnsat_implies_entails f9632 [c9627, c9347, c9478, c2861, c8007, c4461, c3875, c2597] c9632 unsat9632 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9478 := derived9478 a h
  have h3 : Entails.eval a c2861 := h 2860 (by decide)
  have h4 : Entails.eval a c8007 := derived8007 a h
  have h5 : Entails.eval a c4461 := h 4460 (by decide)
  have h6 : Entails.eval a c3875 := h 3874 (by decide)
  have h7 : Entails.eval a c2597 := h 2596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9633 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9633 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2113, some c9631, some c1364, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9633 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9633 : lratChecker f9633 p9633 = .success := by decide +kernel
theorem unsat9633 : Unsatisfiable (PosFin 65) f9633 := by
  apply lratCheckerSound f9633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9633
  · intro a ha; simp [p9633] at ha; subst a; trivial
  · exact checked9633
theorem derived9633 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9633 := by
  apply localUnsat_implies_entails f9633 [c9627, c2113, c9631, c1364] c9633 unsat9633 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2113 := h 2112 (by decide)
  have h2 : Entails.eval a c9631 := derived9631 a h
  have h3 : Entails.eval a c1364 := h 1363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9634 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9634 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9496, some c9627, some c9347, some c9633, some c9478, some c2861, some c9632, some c4726, some c4461, some c3196, some c3871, some c4191, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9634 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9634 : lratChecker f9634 p9634 = .success := by decide +kernel
theorem unsat9634 : Unsatisfiable (PosFin 65) f9634 := by
  apply lratCheckerSound f9634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9634
  · intro a ha; simp [p9634] at ha; subst a; trivial
  · exact checked9634
theorem derived9634 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9634 := by
  apply localUnsat_implies_entails f9634 [c9496, c9627, c9347, c9633, c9478, c2861, c9632, c4726, c4461, c3196, c3871, c4191] c9634 unsat9634 (by rfl) a
  have h0 : Entails.eval a c9496 := derived9496 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9633 := derived9633 a h
  have h4 : Entails.eval a c9478 := derived9478 a h
  have h5 : Entails.eval a c2861 := h 2860 (by decide)
  have h6 : Entails.eval a c9632 := derived9632 a h
  have h7 : Entails.eval a c4726 := h 4725 (by decide)
  have h8 : Entails.eval a c4461 := h 4460 (by decide)
  have h9 : Entails.eval a c3196 := h 3195 (by decide)
  have h10 : Entails.eval a c3871 := h 3870 (by decide)
  have h11 : Entails.eval a c4191 := h 4190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9635 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9635 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2105, some c1387, some c9566, some c3580, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9635 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9635 : lratChecker f9635 p9635 = .success := by decide +kernel
theorem unsat9635 : Unsatisfiable (PosFin 65) f9635 := by
  apply lratCheckerSound f9635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9635
  · intro a ha; simp [p9635] at ha; subst a; trivial
  · exact checked9635
theorem derived9635 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9635 := by
  apply localUnsat_implies_entails f9635 [c9627, c9347, c2105, c1387, c9566, c3580] c9635 unsat9635 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2105 := h 2104 (by decide)
  have h3 : Entails.eval a c1387 := h 1386 (by decide)
  have h4 : Entails.eval a c9566 := derived9566 a h
  have h5 : Entails.eval a c3580 := h 3579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9636 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9636 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9630, some c9496, some c9634, some c9635, some c2846, some c2866, some c2838, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9636 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9636 : lratChecker f9636 p9636 = .success := by decide +kernel
theorem unsat9636 : Unsatisfiable (PosFin 65) f9636 := by
  apply lratCheckerSound f9636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9636
  · intro a ha; simp [p9636] at ha; subst a; trivial
  · exact checked9636
theorem derived9636 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9636 := by
  apply localUnsat_implies_entails f9636 [c9347, c9630, c9496, c9634, c9635, c2846, c2866, c2838] c9636 unsat9636 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9630 := derived9630 a h
  have h2 : Entails.eval a c9496 := derived9496 a h
  have h3 : Entails.eval a c9634 := derived9634 a h
  have h4 : Entails.eval a c9635 := derived9635 a h
  have h5 : Entails.eval a c2846 := h 2845 (by decide)
  have h6 : Entails.eval a c2866 := h 2865 (by decide)
  have h7 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9637 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9637 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2114, some c2100, some c9503, some c8385, some c3785, some c9501, some c2715, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9637 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9637 : lratChecker f9637 p9637 = .success := by decide +kernel
theorem unsat9637 : Unsatisfiable (PosFin 65) f9637 := by
  apply lratCheckerSound f9637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9637
  · intro a ha; simp [p9637] at ha; subst a; trivial
  · exact checked9637
theorem derived9637 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9637 := by
  apply localUnsat_implies_entails f9637 [c9627, c9347, c2114, c2100, c9503, c8385, c3785, c9501, c2715] c9637 unsat9637 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2114 := h 2113 (by decide)
  have h3 : Entails.eval a c2100 := h 2099 (by decide)
  have h4 : Entails.eval a c9503 := derived9503 a h
  have h5 : Entails.eval a c8385 := derived8385 a h
  have h6 : Entails.eval a c3785 := h 3784 (by decide)
  have h7 : Entails.eval a c9501 := derived9501 a h
  have h8 : Entails.eval a c2715 := h 2714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9638 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9638 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2864, some c4893, some c2838, some c3674, some c2851, some c4217, some c2867, some c2871, some c4154, some c2870, some c2889, some c2891, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9638 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9638 : lratChecker f9638 p9638 = .success := by decide +kernel
theorem unsat9638 : Unsatisfiable (PosFin 65) f9638 := by
  apply lratCheckerSound f9638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9638
  · intro a ha; simp [p9638] at ha; subst a; trivial
  · exact checked9638
theorem derived9638 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9638 := by
  apply localUnsat_implies_entails f9638 [c9627, c9347, c2864, c4893, c2838, c3674, c2851, c4217, c2867, c2871, c4154, c2870, c2889, c2891] c9638 unsat9638 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2864 := h 2863 (by decide)
  have h3 : Entails.eval a c4893 := h 4892 (by decide)
  have h4 : Entails.eval a c2838 := h 2837 (by decide)
  have h5 : Entails.eval a c3674 := h 3673 (by decide)
  have h6 : Entails.eval a c2851 := h 2850 (by decide)
  have h7 : Entails.eval a c4217 := h 4216 (by decide)
  have h8 : Entails.eval a c2867 := h 2866 (by decide)
  have h9 : Entails.eval a c2871 := h 2870 (by decide)
  have h10 : Entails.eval a c4154 := h 4153 (by decide)
  have h11 : Entails.eval a c2870 := h 2869 (by decide)
  have h12 : Entails.eval a c2889 := h 2888 (by decide)
  have h13 : Entails.eval a c2891 := h 2890 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9639 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9639 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9637, some c9638, some c9389, some c2149, some c2147, some c8486, some c8631, some c1449, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9639 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9639 : lratChecker f9639 p9639 = .success := by decide +kernel
theorem unsat9639 : Unsatisfiable (PosFin 65) f9639 := by
  apply lratCheckerSound f9639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9639
  · intro a ha; simp [p9639] at ha; subst a; trivial
  · exact checked9639
theorem derived9639 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9639 := by
  apply localUnsat_implies_entails f9639 [c9627, c9637, c9638, c9389, c2149, c2147, c8486, c8631, c1449] c9639 unsat9639 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9637 := derived9637 a h
  have h2 : Entails.eval a c9638 := derived9638 a h
  have h3 : Entails.eval a c9389 := derived9389 a h
  have h4 : Entails.eval a c2149 := h 2148 (by decide)
  have h5 : Entails.eval a c2147 := h 2146 (by decide)
  have h6 : Entails.eval a c8486 := derived8486 a h
  have h7 : Entails.eval a c8631 := derived8631 a h
  have h8 : Entails.eval a c1449 := h 1448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9640 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9640 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2105, some c2114, some c9503, some c9635, some c2576, some c4118, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9640 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9640 : lratChecker f9640 p9640 = .success := by decide +kernel
theorem unsat9640 : Unsatisfiable (PosFin 65) f9640 := by
  apply lratCheckerSound f9640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9640
  · intro a ha; simp [p9640] at ha; subst a; trivial
  · exact checked9640
theorem derived9640 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9640 := by
  apply localUnsat_implies_entails f9640 [c9627, c9347, c2105, c2114, c9503, c9635, c2576, c4118] c9640 unsat9640 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2105 := h 2104 (by decide)
  have h3 : Entails.eval a c2114 := h 2113 (by decide)
  have h4 : Entails.eval a c9503 := derived9503 a h
  have h5 : Entails.eval a c9635 := derived9635 a h
  have h6 : Entails.eval a c2576 := h 2575 (by decide)
  have h7 : Entails.eval a c4118 := h 4117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9641 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9641 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2140, some c2149, some c4119, some c2150, some c2596, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9641 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9641 : lratChecker f9641 p9641 = .success := by decide +kernel
theorem unsat9641 : Unsatisfiable (PosFin 65) f9641 := by
  apply lratCheckerSound f9641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9641
  · intro a ha; simp [p9641] at ha; subst a; trivial
  · exact checked9641
theorem derived9641 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9641 := by
  apply localUnsat_implies_entails f9641 [c9627, c9347, c2140, c2149, c4119, c2150, c2596] c9641 unsat9641 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2140 := h 2139 (by decide)
  have h3 : Entails.eval a c2149 := h 2148 (by decide)
  have h4 : Entails.eval a c4119 := h 4118 (by decide)
  have h5 : Entails.eval a c2150 := h 2149 (by decide)
  have h6 : Entails.eval a c2596 := h 2595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9642 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9642 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2864, some c2846, some c2838, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9642 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9642 : lratChecker f9642 p9642 = .success := by decide +kernel
theorem unsat9642 : Unsatisfiable (PosFin 65) f9642 := by
  apply lratCheckerSound f9642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9642
  · intro a ha; simp [p9642] at ha; subst a; trivial
  · exact checked9642
theorem derived9642 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9642 := by
  apply localUnsat_implies_entails f9642 [c2864, c2846, c2838] c9642 unsat9642 (by rfl) a
  have h0 : Entails.eval a c2864 := h 2863 (by decide)
  have h1 : Entails.eval a c2846 := h 2845 (by decide)
  have h2 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9643 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9643 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9639, some c9640, some c9642, some c9389, some c9641, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9643 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9643 : lratChecker f9643 p9643 = .success := by decide +kernel
theorem unsat9643 : Unsatisfiable (PosFin 65) f9643 := by
  apply lratCheckerSound f9643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9643
  · intro a ha; simp [p9643] at ha; subst a; trivial
  · exact checked9643
theorem derived9643 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9643 := by
  apply localUnsat_implies_entails f9643 [c9347, c9639, c9640, c9642, c9389, c9641] c9643 unsat9643 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9639 := derived9639 a h
  have h2 : Entails.eval a c9640 := derived9640 a h
  have h3 : Entails.eval a c9642 := derived9642 a h
  have h4 : Entails.eval a c9389 := derived9389 a h
  have h5 : Entails.eval a c9641 := derived9641 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9644 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9644 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9643, some c9627, some c8420, some c2113, some c2100, some c1379, some c2107, some c1394, some c9115, some c9195, some c8496, some c8580, some c1307, some c1314, some c1313, some c2071, some c1317, some c687, some c2095, some c8391, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9644 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9644 : lratChecker f9644 p9644 = .success := by decide +kernel
theorem unsat9644 : Unsatisfiable (PosFin 65) f9644 := by
  apply lratCheckerSound f9644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9644
  · intro a ha; simp [p9644] at ha; subst a; trivial
  · exact checked9644
theorem derived9644 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9644 := by
  apply localUnsat_implies_entails f9644 [c9643, c9627, c8420, c2113, c2100, c1379, c2107, c1394, c9115, c9195, c8496, c8580, c1307, c1314, c1313, c2071, c1317, c687, c2095, c8391] c9644 unsat9644 (by rfl) a
  have h0 : Entails.eval a c9643 := derived9643 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c8420 := derived8420 a h
  have h3 : Entails.eval a c2113 := h 2112 (by decide)
  have h4 : Entails.eval a c2100 := h 2099 (by decide)
  have h5 : Entails.eval a c1379 := h 1378 (by decide)
  have h6 : Entails.eval a c2107 := h 2106 (by decide)
  have h7 : Entails.eval a c1394 := h 1393 (by decide)
  have h8 : Entails.eval a c9115 := derived9115 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c8496 := derived8496 a h
  have h11 : Entails.eval a c8580 := derived8580 a h
  have h12 : Entails.eval a c1307 := h 1306 (by decide)
  have h13 : Entails.eval a c1314 := h 1313 (by decide)
  have h14 : Entails.eval a c1313 := h 1312 (by decide)
  have h15 : Entails.eval a c2071 := h 2070 (by decide)
  have h16 : Entails.eval a c1317 := h 1316 (by decide)
  have h17 : Entails.eval a c687 := h 686 (by decide)
  have h18 : Entails.eval a c2095 := h 2094 (by decide)
  have h19 : Entails.eval a c8391 := derived8391 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9645 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9645 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9636, some c9643, some c9627, some c9505, some c3039, some c5043, some c4253, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9645 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9645 : lratChecker f9645 p9645 = .success := by decide +kernel
theorem unsat9645 : Unsatisfiable (PosFin 65) f9645 := by
  apply lratCheckerSound f9645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9645
  · intro a ha; simp [p9645] at ha; subst a; trivial
  · exact checked9645
theorem derived9645 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9645 := by
  apply localUnsat_implies_entails f9645 [c9636, c9643, c9627, c9505, c3039, c5043, c4253] c9645 unsat9645 (by rfl) a
  have h0 : Entails.eval a c9636 := derived9636 a h
  have h1 : Entails.eval a c9643 := derived9643 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9505 := derived9505 a h
  have h4 : Entails.eval a c3039 := h 3038 (by decide)
  have h5 : Entails.eval a c5043 := h 5042 (by decide)
  have h6 : Entails.eval a c4253 := h 4252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9646 : DefaultClause 65 := directClause [(⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9646 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9636, some c9644, some c9643, some c9347, some c9645, some c2861, some c2851, some c9115, some c9195, some c8496, some c8580, some c2823, some c2831, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9646 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9646 : lratChecker f9646 p9646 = .success := by decide +kernel
theorem unsat9646 : Unsatisfiable (PosFin 65) f9646 := by
  apply lratCheckerSound f9646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9646
  · intro a ha; simp [p9646] at ha; subst a; trivial
  · exact checked9646
theorem derived9646 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9646 := by
  apply localUnsat_implies_entails f9646 [c9636, c9644, c9643, c9347, c9645, c2861, c2851, c9115, c9195, c8496, c8580, c2823, c2831] c9646 unsat9646 (by rfl) a
  have h0 : Entails.eval a c9636 := derived9636 a h
  have h1 : Entails.eval a c9644 := derived9644 a h
  have h2 : Entails.eval a c9643 := derived9643 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9645 := derived9645 a h
  have h5 : Entails.eval a c2861 := h 2860 (by decide)
  have h6 : Entails.eval a c2851 := h 2850 (by decide)
  have h7 : Entails.eval a c9115 := derived9115 a h
  have h8 : Entails.eval a c9195 := derived9195 a h
  have h9 : Entails.eval a c8496 := derived8496 a h
  have h10 : Entails.eval a c8580 := derived8580 a h
  have h11 : Entails.eval a c2823 := h 2822 (by decide)
  have h12 : Entails.eval a c2831 := h 2830 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9647 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9647 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9636, some c9643, some c9347, some c9644, some c9646, some c9405, some c9416, some c2861, some c2860, some c2865, some c2868, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9647 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9647 : lratChecker f9647 p9647 = .success := by decide +kernel
theorem unsat9647 : Unsatisfiable (PosFin 65) f9647 := by
  apply lratCheckerSound f9647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9647
  · intro a ha; simp [p9647] at ha; subst a; trivial
  · exact checked9647
theorem derived9647 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9647 := by
  apply localUnsat_implies_entails f9647 [c9636, c9643, c9347, c9644, c9646, c9405, c9416, c2861, c2860, c2865, c2868] c9647 unsat9647 (by rfl) a
  have h0 : Entails.eval a c9636 := derived9636 a h
  have h1 : Entails.eval a c9643 := derived9643 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9644 := derived9644 a h
  have h4 : Entails.eval a c9646 := derived9646 a h
  have h5 : Entails.eval a c9405 := derived9405 a h
  have h6 : Entails.eval a c9416 := derived9416 a h
  have h7 : Entails.eval a c2861 := h 2860 (by decide)
  have h8 : Entails.eval a c2860 := h 2859 (by decide)
  have h9 : Entails.eval a c2865 := h 2864 (by decide)
  have h10 : Entails.eval a c2868 := h 2867 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9648 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9648 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9635, some c2846, some c2866, some c2838, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9648 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9648 : lratChecker f9648 p9648 = .success := by decide +kernel
theorem unsat9648 : Unsatisfiable (PosFin 65) f9648 := by
  apply lratCheckerSound f9648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9648
  · intro a ha; simp [p9648] at ha; subst a; trivial
  · exact checked9648
theorem derived9648 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9648 := by
  apply localUnsat_implies_entails f9648 [c9347, c9635, c2846, c2866, c2838] c9648 unsat9648 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9635 := derived9635 a h
  have h2 : Entails.eval a c2846 := h 2845 (by decide)
  have h3 : Entails.eval a c2866 := h 2865 (by decide)
  have h4 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9649 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9649 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9636, some c9647, some c9648, some c9389, some c9645, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9649 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9649 : lratChecker f9649 p9649 = .success := by decide +kernel
theorem unsat9649 : Unsatisfiable (PosFin 65) f9649 := by
  apply lratCheckerSound f9649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9649
  · intro a ha; simp [p9649] at ha; subst a; trivial
  · exact checked9649
theorem derived9649 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9649 := by
  apply localUnsat_implies_entails f9649 [c9636, c9647, c9648, c9389, c9645] c9649 unsat9649 (by rfl) a
  have h0 : Entails.eval a c9636 := derived9636 a h
  have h1 : Entails.eval a c9647 := derived9647 a h
  have h2 : Entails.eval a c9648 := derived9648 a h
  have h3 : Entails.eval a c9389 := derived9389 a h
  have h4 : Entails.eval a c9645 := derived9645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9650 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9650 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9649, some c9504, some c9498, some c9347, some c1286, some c1271, some c9644, some c9576, some c1300, some c1294, some c9505, some c9401, some c9115, some c9574, some c8490, some c2831, some c2823, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9650 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9650 : lratChecker f9650 p9650 = .success := by decide +kernel
theorem unsat9650 : Unsatisfiable (PosFin 65) f9650 := by
  apply lratCheckerSound f9650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9650
  · intro a ha; simp [p9650] at ha; subst a; trivial
  · exact checked9650
theorem derived9650 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9650 := by
  apply localUnsat_implies_entails f9650 [c9649, c9504, c9498, c9347, c1286, c1271, c9644, c9576, c1300, c1294, c9505, c9401, c9115, c9574, c8490, c2831, c2823] c9650 unsat9650 (by rfl) a
  have h0 : Entails.eval a c9649 := derived9649 a h
  have h1 : Entails.eval a c9504 := derived9504 a h
  have h2 : Entails.eval a c9498 := derived9498 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c1286 := h 1285 (by decide)
  have h5 : Entails.eval a c1271 := h 1270 (by decide)
  have h6 : Entails.eval a c9644 := derived9644 a h
  have h7 : Entails.eval a c9576 := derived9576 a h
  have h8 : Entails.eval a c1300 := h 1299 (by decide)
  have h9 : Entails.eval a c1294 := h 1293 (by decide)
  have h10 : Entails.eval a c9505 := derived9505 a h
  have h11 : Entails.eval a c9401 := derived9401 a h
  have h12 : Entails.eval a c9115 := derived9115 a h
  have h13 : Entails.eval a c9574 := derived9574 a h
  have h14 : Entails.eval a c8490 := derived8490 a h
  have h15 : Entails.eval a c2831 := h 2830 (by decide)
  have h16 : Entails.eval a c2823 := h 2822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9650

end CochromaticTwenty.Certificates.FixedCore0
