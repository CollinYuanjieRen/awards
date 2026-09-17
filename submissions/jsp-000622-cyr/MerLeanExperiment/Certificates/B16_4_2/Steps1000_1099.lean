import MerLeanExperiment.Certificates.B16_4_2.Steps0900_0999

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1384 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨16, by decide⟩, true), (⟨38, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c676, some c20, some c32, some c1303, some c1367, some c272, some c1094, some c674, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c358, c676, c20, c32, c1303, c1367, c272, c1094, c674] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c676 := derived676 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c1094 := derived1094 a h
  have h8 : Entails.eval a c674 := derived674 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c354, some c358, some c4, some c1379, some c1, some c1324, some c1282, some c1352, some c1384, some c1353, some c6, some c114, some c142, some c1360, some c164, some c554, some c58, some c359, some c360, some c36, some c318, some c317, some c462, some c155, some c1062, some c275, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1383, c354, c358, c4, c1379, c1, c1324, c1282, c1352, c1384, c1353, c6, c114, c142, c1360, c164, c554, c58, c359, c360, c36, c318, c317, c462, c155, c1062, c275] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c1379 := derived1379 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1324 := derived1324 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c1352 := derived1352 a h
  have h9 : Entails.eval a c1384 := derived1384 a h
  have h10 : Entails.eval a c1353 := derived1353 a h
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c1360 := derived1360 a h
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c554 := derived554 a h
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c359 := h 358 (by decide)
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c317 := h 316 (by decide)
  have h23 : Entails.eval a c462 := derived462 a h
  have h24 : Entails.eval a c155 := h 154 (by decide)
  have h25 : Entails.eval a c1062 := derived1062 a h
  have h26 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c1383, some c1379, some c1, some c1324, some c1282, some c358, some c354, some c1385, some c30, some c19, some c1367, some c128, some c137, some c135, some c139, some c84, some c80, some c1139, some c204, some c176, some c360, some c662, some c465, some c265, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c4, c1383, c1379, c1, c1324, c1282, c358, c354, c1385, c30, c19, c1367, c128, c137, c135, c139, c84, c80, c1139, c204, c176, c360, c662, c465, c265] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1379 := derived1379 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c1385 := derived1385 a h
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c1367 := derived1367 a h
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c80 := h 79 (by decide)
  have h18 : Entails.eval a c1139 := derived1139 a h
  have h19 : Entails.eval a c204 := h 203 (by decide)
  have h20 : Entails.eval a c176 := h 175 (by decide)
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c662 := derived662 a h
  have h23 : Entails.eval a c465 := derived465 a h
  have h24 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1, some c1324, some c1282, some c4, some c1386, some c667, some c1351, some c19, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1379, c1, c1324, c1282, c4, c1386, c667, c1351, c19] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1386 := derived1386 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c1351 := derived1351 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1379, some c1, some c1282, some c1384, some c1353, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c1383, c1379, c1, c1282, c1384, c1353] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1379 := derived1379 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1384 := derived1384 a h
  have h5 : Entails.eval a c1353 := derived1353 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c892, some c729, some c145, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 57) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c116, c892, c729, c145] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c892 := derived892 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c354, some c358, some c1387, some c1379, some c1, some c1324, some c1282, some c39, some c1360, some c1388, some c202, some c203, some c1389, some c6, some c33, some c1303, some c723, some c225, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 57) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1383, c354, c358, c1387, c1379, c1, c1324, c1282, c39, c1360, c1388, c202, c203, c1389, c6, c33, c1303, c723, c225] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1379 := derived1379 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1324 := derived1324 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c1360 := derived1360 a h
  have h10 : Entails.eval a c1388 := derived1388 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c1389 := derived1389 a h
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c1303 := derived1303 a h
  have h17 : Entails.eval a c723 := derived723 a h
  have h18 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c142, some c1360, some c58, some c59, some c318, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 57) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c142, c1360, c58, c59, c318] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c142 := h 141 (by decide)
  have h1 : Entails.eval a c1360 := derived1360 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1387, some c1383, some c358, some c1391, some c354, some c1379, some c1, some c1352, some c1384, some c6, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 57) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c1282, c1324, c1387, c1383, c358, c1391, c354, c1379, c1, c1352, c1384, c6] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1391 := derived1391 a h
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c1379 := derived1379 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c1352 := derived1352 a h
  have h10 : Entails.eval a c1384 := derived1384 a h
  have h11 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c358, some c1387, some c1324, some c1282, some c1390, some c1391, some c1392, some c203, some c1364, some c6, some c33, some c20, some c32, some c1303, some c359, some c1094, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 57) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c1383, c358, c1387, c1324, c1282, c1390, c1391, c1392, c203, c1364, c6, c33, c20, c32, c1303, c359, c1094] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1324 := derived1324 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1390 := derived1390 a h
  have h6 : Entails.eval a c1391 := derived1391 a h
  have h7 : Entails.eval a c1392 := derived1392 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c1364 := derived1364 a h
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c1303 := derived1303 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1394 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1387, some c1383, some c1324, some c1282, some c1393, some c30, some c31, some c1367, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 57) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c1387, c1383, c1324, c1282, c1393, c30, c31, c1367] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c1387 := derived1387 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1393 := derived1393 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c1367 := derived1367 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨40, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c202, some c745, some c727, some c36, some c270, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 57) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c203, c202, c745, c727, c36, c270] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c745 := derived745 a h
  have h3 : Entails.eval a c727 := derived727 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c1379, some c1, some c1387, some c1324, some c71, some c667, some c203, some c1282, some c24, some c1303, some c1364, some c1395, some c6, some c20, some c32, some c1274, some c1094, some c359, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 57) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c1394, c1379, c1, c1387, c1324, c71, c667, c203, c1282, c24, c1303, c1364, c1395, c6, c20, c32, c1274, c1094, c359] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c1379 := derived1379 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c1303 := derived1303 a h
  have h11 : Entails.eval a c1364 := derived1364 a h
  have h12 : Entails.eval a c1395 := derived1395 a h
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c1274 := derived1274 a h
  have h17 : Entails.eval a c1094 := derived1094 a h
  have h18 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1, some c1324, some c1282, some c1387, some c1394, some c71, some c667, some c202, some c1396, some c30, some c854, some c58, some c64, some c158, some c320, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 57) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1379, c1, c1324, c1282, c1387, c1394, c71, c667, c202, c1396, c30, c854, c58, c64, c158, c320] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c1394 := derived1394 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c1396 := derived1396 a h
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c854 := derived854 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1, some c1397, some c271, some c125, some c77, some c1095, some c638, some c268, some c1324, some c1282, some c4, some c139, some c1303, some c734, some c237, some c84, some c179, some c330, some c374, some c70, some c1329, some c181, some c6, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 57) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c1379, c1, c1397, c271, c125, c77, c1095, c638, c268, c1324, c1282, c4, c139, c1303, c734, c237, c84, c179, c330, c374, c70, c1329, c181, c6] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1397 := derived1397 a h
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c1095 := derived1095 a h
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c1324 := derived1324 a h
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c1303 := derived1303 a h
  have h14 : Entails.eval a c734 := derived734 a h
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  have h18 : Entails.eval a c330 := h 329 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c1329 := derived1329 a h
  have h22 : Entails.eval a c181 := h 180 (by decide)
  have h23 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c1114, some c358, some c225, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c70, c1114, c358, c225] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c1114 := derived1114 a h
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1398, some c1397, some c271, some c1095, some c268, some c1324, some c1282, some c1303, some c1399, some c360, some c465, some c462, some c219, some c224, some c59, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1398, c1397, c271, c1095, c268, c1324, c1282, c1303, c1399, c360, c465, c462, c219, c224, c59] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1397 := derived1397 a h
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c1095 := derived1095 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1303 := derived1303 a h
  have h8 : Entails.eval a c1399 := derived1399 a h
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c465 := derived465 a h
  have h11 : Entails.eval a c462 := derived462 a h
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c271, some c125, some c1095, some c638, some c1324, some c1282, some c70, some c39, some c1329, some c602, some c6, some c88, some c156, some c180, some c219, some c334, some c465, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1, c271, c125, c1095, c638, c1324, c1282, c70, c39, c1329, c602, c6, c88, c156, c180, c219, c334, c465] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c1095 := derived1095 a h
  have h4 : Entails.eval a c638 := derived638 a h
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c1329 := derived1329 a h
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c180 := h 179 (by decide)
  have h15 : Entails.eval a c219 := h 218 (by decide)
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c465 := derived465 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1397, some c1379, some c1, some c271, some c638, some c1095, some c1400, some c139, some c203, some c1401, some c1243, some c360, some c792, some c72, some c6, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1397, c1379, c1, c271, c638, c1095, c1400, c139, c203, c1401, c1243, c360, c792, c72, c6] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1397 := derived1397 a h
  have h1 : Entails.eval a c1379 := derived1379 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c638 := derived638 a h
  have h5 : Entails.eval a c1095 := derived1095 a h
  have h6 : Entails.eval a c1400 := derived1400 a h
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c1401 := derived1401 a h
  have h10 : Entails.eval a c1243 := derived1243 a h
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c792 := derived792 a h
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨40, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c269, some c1303, some c1367, some c76, some c42, some c658, some c360, some c355, some c223, some c170, some c1355, some c157, some c706, some c205, some c123, some c122, some c325, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c269, c1303, c1367, c76, c42, c658, c360, c355, c223, c170, c1355, c157, c706, c205, c123, c122, c325] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1367 := derived1367 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c658 := derived658 a h
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c1355 := derived1355 a h
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c706 := derived706 a h
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c122 := h 121 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨48, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c80, some c237, some c265, some c465, some c241, some c336, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c84, c80, c237, c265, c465, c241, c336] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c465 := derived465 a h
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1397, some c1282, some c1324, some c1402, some c30, some c269, some c19, some c1379, some c1, some c1403, some c139, some c128, some c1404, some c31, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1397, c1282, c1324, c1402, c30, c269, c19, c1379, c1, c1403, c139, c128, c1404, c31] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1397 := derived1397 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1402 := derived1402 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c1379 := derived1379 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c1403 := derived1403 a h
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c128 := h 127 (by decide)
  have h12 : Entails.eval a c1404 := derived1404 a h
  have h13 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1, some c1324, some c1282, some c1402, some c30, some c19, some c1405, some c202, some c4, some c31, some c1367, some c76, some c170, some c360, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c1379, c1, c1324, c1282, c1402, c30, c19, c1405, c202, c4, c31, c1367, c76, c170, c360] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1402 := derived1402 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c1405 := derived1405 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c1367 := derived1367 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1406, some c1397, some c1379, some c1, some c1324, some c1282, some c271, some c638, some c1351, some c1398, some c1095, some c203, some c71, some c359, some c792, some c73, some c6, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c1406, c1397, c1379, c1, c1324, c1282, c271, c638, c1351, c1398, c1095, c203, c71, c359, c792, c73, c6] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c1406 := derived1406 a h
  have h1 : Entails.eval a c1397 := derived1397 a h
  have h2 : Entails.eval a c1379 := derived1379 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1324 := derived1324 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c1351 := derived1351 a h
  have h9 : Entails.eval a c1398 := derived1398 a h
  have h10 : Entails.eval a c1095 := derived1095 a h
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c359 := h 358 (by decide)
  have h14 : Entails.eval a c792 := derived792 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1379, some c1324, some c1282, some c1, some c1406, some c1407, some c30, some c19, some c854, some c667, some c58, some c64, some c202, some c320, some c158, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1379, c1324, c1282, c1, c1406, c1407, c30, c19, c854, c667, c58, c64, c202, c320, c158] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1379 := derived1379 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1406 := derived1406 a h
  have h5 : Entails.eval a c1407 := derived1407 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c854 := derived854 a h
  have h9 : Entails.eval a c667 := derived667 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1408, some c1282, some c631, some c1303, some c120, some c1299, some c354, some c141, some c358, some c161, some c128, some c335, some c1379, some c137, some c205, some c6, some c126, some c676, some c815, some c210, some c64, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c1408, c1282, c631, c1303, c120, c1299, c354, c141, c358, c161, c128, c335, c1379, c137, c205, c6, c126, c676, c815, c210, c64] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c1408 := derived1408 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1303 := derived1303 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c1299 := derived1299 a h
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c1379 := derived1379 a h
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  have h17 : Entails.eval a c676 := derived676 a h
  have h18 : Entails.eval a c815 := derived815 a h
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c141, some c1329, some c602, some c162, some c12, some c157, some c208, some c315, some c1246, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c354, c141, c1329, c602, c162, c12, c157, c208, c315, c1246] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c1329 := derived1329 a h
  have h3 : Entails.eval a c602 := derived602 a h
  have h4 : Entails.eval a c162 := h 161 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c1246 := derived1246 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1408, some c631, some c1303, some c1379, some c1324, some c1299, some c120, some c358, some c354, some c1409, some c271, some c1138, some c139, some c1410, some c1243, some c360, some c72, some c163, some c12, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c1282, c1408, c631, c1303, c1379, c1324, c1299, c120, c358, c354, c1409, c271, c1138, c139, c1410, c1243, c360, c72, c163, c12] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1303 := derived1303 a h
  have h4 : Entails.eval a c1379 := derived1379 a h
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1299 := derived1299 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c1409 := derived1409 a h
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c1138 := derived1138 a h
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c1410 := derived1410 a h
  have h15 : Entails.eval a c1243 := derived1243 a h
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c70, some c39, some c1373, some c358, some c354, some c33, some c161, some c141, some c162, some c6, some c206, some c163, some c124, some c333, some c88, some c126, some c182, some c210, some c208, some c64, some c136, some c219, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1282, c631, c1303, c70, c39, c1373, c358, c354, c33, c161, c141, c162, c6, c206, c163, c124, c333, c88, c126, c182, c210, c208, c64, c136, c219] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c1373 := derived1373 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c126 := h 125 (by decide)
  have h19 : Entails.eval a c182 := h 181 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c136 := h 135 (by decide)
  have h24 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨10, by decide⟩, true), (⟨40, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c161, some c114, some c142, some c354, some c554, some c22, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c161, c114, c142, c354, c554, c22] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c161 := h 160 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c554 := derived554 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c116, some c12, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 57) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c20, c116, c12] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c22, some c76, some c42, some c355, some c210, some c141, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 57) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c631, c22, c76, c42, c355, c210, c141] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1415, some c354, some c141, some c1412, some c631, some c1303, some c1414, some c356, some c1413, some c8, some c206, some c33, some c6, some c124, some c329, some c333, some c126, some c178, some c210, some c208, some c58, some c64, some c136, some c219, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 57) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1282, c1415, c354, c141, c1412, c631, c1303, c1414, c356, c1413, c8, c206, c33, c6, c124, c329, c333, c126, c178, c210, c208, c58, c64, c136, c219] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1415 := derived1415 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c1412 := derived1412 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c1414 := derived1414 a h
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c1413 := derived1413 a h
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  have h18 : Entails.eval a c178 := h 177 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c136 := h 135 (by decide)
  have h24 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1415, some c354, some c1416, some c358, some c161, some c8, some c206, some c33, some c6, some c116, some c124, some c88, some c333, some c182, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 57) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c1282, c631, c1303, c1415, c354, c1416, c358, c161, c8, c206, c33, c6, c116, c124, c88, c333, c182] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1415 := derived1415 a h
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c1416 := derived1416 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1282, some c356, some c359, some c161, some c114, some c1092, some c1149, some c1159, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 57) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c631, c1282, c356, c359, c161, c114, c1092, c1149, c1159] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c1092 := derived1092 a h
  have h7 : Entails.eval a c1149 := derived1149 a h
  have h8 : Entails.eval a c1159 := derived1159 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1417, some c24, some c233, some c8, some c1418, some c70, some c1373, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 57) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1282, c631, c1303, c1417, c24, c233, c8, c1418, c70, c1373] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1417 := derived1417 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1418 := derived1418 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c1373 := derived1373 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨10, by decide⟩, false), (⟨33, by decide⟩, true), (⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1243, some c360, some c72, some c163, some c6, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 57) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c1243, c360, c72, c163, c6] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c1243 := derived1243 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c219, some c315, some c36, some c52, some c210, some c351, some c50, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 57) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c219, c315, c36, c52, c210, c351, c50] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c631, some c1282, some c1415, some c358, some c354, some c1413, some c1138, some c141, some c8, some c206, some c1420, some c39, some c1329, some c602, some c162, some c6, some c1421, some c64, some c156, some c210, some c208, some c138, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 57) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c271, c631, c1282, c1415, c358, c354, c1413, c1138, c141, c8, c206, c1420, c39, c1329, c602, c162, c6, c1421, c64, c156, c210, c208, c138] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1415 := derived1415 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c1413 := derived1413 a h
  have h7 : Entails.eval a c1138 := derived1138 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c1420 := derived1420 a h
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c1329 := derived1329 a h
  have h14 : Entails.eval a c602 := derived602 a h
  have h15 : Entails.eval a c162 := h 161 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c1421 := derived1421 a h
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨34, by decide⟩, false), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c1329, some c602, some c357, some c12, some c144, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 57) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c70, c1329, c602, c357, c12, c144] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c1329 := derived1329 a h
  have h2 : Entails.eval a c602 := derived602 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1408, some c631, some c1303, some c1379, some c1324, some c1411, some c1419, some c268, some c271, some c1422, some c24, some c235, some c8, some c638, some c114, some c122, some c84, some c247, some c77, some c1423, some c1243, some c360, some c325, some c72, some c174, some c12, some c208, some c792, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 57) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1282, c1408, c631, c1303, c1379, c1324, c1411, c1419, c268, c271, c1422, c24, c235, c8, c638, c114, c122, c84, c247, c77, c1423, c1243, c360, c325, c72, c174, c12, c208, c792] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1303 := derived1303 a h
  have h4 : Entails.eval a c1379 := derived1379 a h
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1411 := derived1411 a h
  have h7 : Entails.eval a c1419 := derived1419 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c1422 := derived1422 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c638 := derived638 a h
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c77 := h 76 (by decide)
  have h20 : Entails.eval a c1423 := derived1423 a h
  have h21 : Entails.eval a c1243 := derived1243 a h
  have h22 : Entails.eval a c360 := h 359 (by decide)
  have h23 : Entails.eval a c325 := h 324 (by decide)
  have h24 : Entails.eval a c72 := h 71 (by decide)
  have h25 : Entails.eval a c174 := h 173 (by decide)
  have h26 : Entails.eval a c12 := h 11 (by decide)
  have h27 : Entails.eval a c208 := h 207 (by decide)
  have h28 : Entails.eval a c792 := derived792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c122, some c84, some c325, some c243, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 57) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c114, c122, c84, c325, c243] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c358, some c354, some c161, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 57) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1415, c358, c354, c161] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨8, by decide⟩, false), (⟨35, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c631, some c1303, some c1425, some c269, some c1426, some c233, some c1418, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 57) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c1282, c631, c1303, c1425, c269, c1426, c233, c1418] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c1425 := derived1425 a h
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c1426 := derived1426 a h
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c1418 := derived1418 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1282, some c1408, some c631, some c1303, some c1424, some c30, some c19, some c31, some c1427, some c1100, some c8, some c204, some c1299, some c120, some c137, some c358, some c354, some c141, some c163, some c210, some c359, some c58, some c50, some c64, some c351, some c261, some c320, some c315, some c309, some c276, some c316, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 57) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c1324, c1282, c1408, c631, c1303, c1424, c30, c19, c31, c1427, c1100, c8, c204, c1299, c120, c137, c358, c354, c141, c163, c210, c359, c58, c50, c64, c351, c261, c320, c315, c309, c276, c316] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1408 := derived1408 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c1424 := derived1424 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c1427 := derived1427 a h
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c1299 := derived1299 a h
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c358 := h 357 (by decide)
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c141 := h 140 (by decide)
  have h19 : Entails.eval a c163 := h 162 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c58 := h 57 (by decide)
  have h23 : Entails.eval a c50 := h 49 (by decide)
  have h24 : Entails.eval a c64 := h 63 (by decide)
  have h25 : Entails.eval a c351 := h 350 (by decide)
  have h26 : Entails.eval a c261 := h 260 (by decide)
  have h27 : Entails.eval a c320 := h 319 (by decide)
  have h28 : Entails.eval a c315 := h 314 (by decide)
  have h29 : Entails.eval a c309 := h 308 (by decide)
  have h30 : Entails.eval a c276 := h 275 (by decide)
  have h31 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c35, some c266, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 57) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c34, c35, c266] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1429, some c39, some c1114, some c218, some c141, some c62, some c63, some c314, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 57) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c631, c1429, c39, c1114, c218, c141, c62, c63, c314] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1429 := derived1429 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c1114 := derived1114 a h
  have h4 : Entails.eval a c218 := h 217 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c360, some c525, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 57) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c359, c360, c525] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c525 := derived525 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1429, some c75, some c41, some c74, some c209, some c354, some c141, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 57) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c631, c1429, c75, c41, c74, c209, c354, c141] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1429 := derived1429 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c631, some c1429, some c1430, some c1431, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 57) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1432, c631, c1429, c1430, c1431] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1429 := derived1429 a h
  have h3 : Entails.eval a c1430 := derived1430 a h
  have h4 : Entails.eval a c1431 := derived1431 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1433, some c30, some c31, some c266, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 57) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c631, c1433, c30, c31, c266] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1433 := derived1433 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c268, some c271, some c1399, some c1429, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 57) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c71, c268, c271, c1399, c1429] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c1399 := derived1399 a h
  have h4 : Entails.eval a c1429 := derived1429 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c267, some c140, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 57) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c266, c267, c140] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c70, some c39, some c71, some c358, some c1360, some c1435, some c1359, some c6, some c33, some c205, some c1436, some c1399, some c270, some c140, some c34, some c272, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 57) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1282, c70, c39, c71, c358, c1360, c1435, c1359, c6, c33, c205, c1436, c1399, c270, c140, c34, c272] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1360 := derived1360 a h
  have h6 : Entails.eval a c1435 := derived1435 a h
  have h7 : Entails.eval a c1359 := derived1359 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c1436 := derived1436 a h
  have h12 : Entails.eval a c1399 := derived1399 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1428, some c105, some c107, some c1282, some c1434, some c3, some c1437, some c35, some c1095, some c360, some c465, some c462, some c219, some c224, some c59, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 57) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c1324, c1428, c105, c107, c1282, c1434, c3, c1437, c35, c1095, c360, c465, c462, c219, c224, c59] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1428 := derived1428 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1434 := derived1434 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c1437 := derived1437 a h
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c1095 := derived1095 a h
  have h10 : Entails.eval a c360 := h 359 (by decide)
  have h11 : Entails.eval a c465 := derived465 a h
  have h12 : Entails.eval a c462 := derived462 a h
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1428, some c1282, some c1324, some c105, some c107, some c1434, some c3, some c1437, some c1438, some c271, some c272, some c1431, some c1364, some c465, some c75, some c41, some c74, some c355, some c218, some c358, some c58, some c59, some c1391, some c314, some c847, some c205, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 57) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1428, c1282, c1324, c105, c107, c1434, c3, c1437, c1438, c271, c272, c1431, c1364, c465, c75, c41, c74, c355, c218, c358, c58, c59, c1391, c314, c847, c205] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1434 := derived1434 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c1437 := derived1437 a h
  have h8 : Entails.eval a c1438 := derived1438 a h
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c1431 := derived1431 a h
  have h12 : Entails.eval a c1364 := derived1364 a h
  have h13 : Entails.eval a c465 := derived465 a h
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c41 := h 40 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c355 := h 354 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  have h19 : Entails.eval a c358 := h 357 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c59 := h 58 (by decide)
  have h22 : Entails.eval a c1391 := derived1391 a h
  have h23 : Entails.eval a c314 := h 313 (by decide)
  have h24 : Entails.eval a c847 := derived847 a h
  have h25 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c354, some c225, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 57) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c358, c354, c225] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1428, some c107, some c1324, some c1439, some c31, some c19, some c1282, some c30, some c105, some c1434, some c42, some c74, some c223, some c360, some c59, some c63, some c462, some c320, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 57) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1428, c107, c1324, c1439, c31, c19, c1282, c30, c105, c1434, c42, c74, c223, c360, c59, c63, c462, c320] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1324 := derived1324 a h
  have h3 : Entails.eval a c1439 := derived1439 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c1434 := derived1434 a h
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c462 := derived462 a h
  have h17 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1442 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c1324, some c1428, some c105, some c107, some c1434, some c1439, some c30, some c19, some c31, some c270, some c266, some c1441, some c1440, some c75, some c854, some c360, some c58, some c62, some c462, some c320, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 57) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c1282, c1324, c1428, c105, c107, c1434, c1439, c30, c19, c31, c270, c266, c1441, c1440, c75, c854, c360, c58, c62, c462, c320] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c1324 := derived1324 a h
  have h2 : Entails.eval a c1428 := derived1428 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1434 := derived1434 a h
  have h6 : Entails.eval a c1439 := derived1439 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c1441 := derived1441 a h
  have h13 : Entails.eval a c1440 := derived1440 a h
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c854 := derived854 a h
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c462 := derived462 a h
  have h20 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1443 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1442, some c1434, some c105, some c1303, some c31, some c24, some c1415, some c358, some c38, some c18, some c213, some c58, some c59, some c318, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 57) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c631, c1442, c1434, c105, c1303, c31, c24, c1415, c358, c38, c18, c213, c58, c59, c318] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1442 := derived1442 a h
  have h2 : Entails.eval a c1434 := derived1434 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1415 := derived1415 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨34, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1303, some c24, some c1415, some c358, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 57) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c631, c1303, c24, c1415, c358] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c1415 := derived1415 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1444, some c112, some c1432, some c631, some c1429, some c1431, some c272, some c358, some c22, some c42, some c210, some c141, some c355, some c703, some c143, some c218, some c56, some c63, some c318, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 57) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1077, c1444, c112, c1432, c631, c1429, c1431, c272, c358, c22, c42, c210, c141, c355, c703, c143, c218, c56, c63, c318] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1432 := derived1432 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1429 := derived1429 a h
  have h6 : Entails.eval a c1431 := derived1431 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c703 := derived703 a h
  have h15 : Entails.eval a c143 := h 142 (by decide)
  have h16 : Entails.eval a c218 := h 217 (by decide)
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c63 := h 62 (by decide)
  have h19 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1077, some c1444, some c112, some c1429, some c1432, some c1445, some c24, some c44, some c266, some c212, some c22, some c141, some c357, some c353, some c525, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 57) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c631, c1077, c1444, c112, c1429, c1432, c1445, c24, c44, c266, c212, c22, c141, c357, c353, c525] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1429 := derived1429 a h
  have h5 : Entails.eval a c1432 := derived1432 a h
  have h6 : Entails.eval a c1445 := derived1445 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c525 := derived525 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c631, some c358, some c22, some c42, some c210, some c141, some c355, some c703, some c115, some c123, some c356, some c87, some c325, some c232, some c241, some c269, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 57) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1077, c631, c358, c22, c42, c210, c141, c355, c703, c115, c123, c356, c87, c325, c232, c241, c269] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c703 := derived703 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c325 := h 324 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1442, some c1443, some c1077, some c1444, some c112, some c1432, some c1429, some c1446, some c265, some c1447, some c24, some c44, some c266, some c212, some c22, some c141, some c1199, some c353, some c703, some c115, some c134, some c123, some c87, some c325, some c85, some c248, some c322, some c175, some c173, some c205, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 57) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c631, c1442, c1443, c1077, c1444, c112, c1432, c1429, c1446, c265, c1447, c24, c44, c266, c212, c22, c141, c1199, c353, c703, c115, c134, c123, c87, c325, c85, c248, c322, c175, c173, c205] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1442 := derived1442 a h
  have h2 : Entails.eval a c1443 := derived1443 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1444 := derived1444 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1432 := derived1432 a h
  have h7 : Entails.eval a c1429 := derived1429 a h
  have h8 : Entails.eval a c1446 := derived1446 a h
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c1447 := derived1447 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  have h17 : Entails.eval a c1199 := derived1199 a h
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c703 := derived703 a h
  have h20 : Entails.eval a c115 := h 114 (by decide)
  have h21 : Entails.eval a c134 := h 133 (by decide)
  have h22 : Entails.eval a c123 := h 122 (by decide)
  have h23 : Entails.eval a c87 := h 86 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  have h25 : Entails.eval a c85 := h 84 (by decide)
  have h26 : Entails.eval a c248 := h 247 (by decide)
  have h27 : Entails.eval a c322 := h 321 (by decide)
  have h28 : Entails.eval a c175 := h 174 (by decide)
  have h29 : Entails.eval a c173 := h 172 (by decide)
  have h30 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1415, some c354, some c358, some c141, some c38, some c18, some c69, some c554, some c213, some c36, some c39, some c47, some c211, some c347, some c51, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 57) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c631, c1415, c354, c358, c141, c38, c18, c69, c554, c213, c36, c39, c47, c211, c347, c51] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1415 := derived1415 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c554 := derived554 a h
  have h9 : Entails.eval a c213 := h 212 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c18, some c213, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 57) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c38, c18, c213] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c39, some c1450, some c357, some c233, some c268, some c602, some c29, some c281, some c219, some c64, some c57, some c318, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 57) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c70, c39, c1450, c357, c233, c268, c602, c29, c281, c219, c64, c57, c318] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c602 := derived602 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c281 := h 280 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1303, some c1451, some c38, some c18, some c69, some c554, some c360, some c36, some c1092, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 57) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1303, c1451, c38, c18, c69, c554, c360, c36, c1092] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1303 := derived1303 a h
  have h1 : Entails.eval a c1451 := derived1451 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c554 := derived554 a h
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c1092 := derived1092 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c271, some c29, some c235, some c360, some c43, some c219, some c47, some c259, some c341, some c97, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 57) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c268, c271, c29, c235, c360, c43, c219, c47, c259, c341, c97] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c219 := h 218 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨2, by decide⟩, true), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1453, some c356, some c233, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 57) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c1453, c356, c233] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c1453 := derived1453 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1303, some c1449, some c1451, some c1452, some c1454, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 57) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c631, c1303, c1449, c1451, c1452, c1454] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1449 := derived1449 a h
  have h3 : Entails.eval a c1451 := derived1451 a h
  have h4 : Entails.eval a c1452 := derived1452 a h
  have h5 : Entails.eval a c1454 := derived1454 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1455, some c19, some c30, some c1415, some c354, some c358, some c141, some c38, some c18, some c69, some c773, some c269, some c360, some c58, some c50, some c64, some c1368, some c316, some c351, some c320, some c315, some c309, some c145, some c349, some c1414, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 57) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c1455, c19, c30, c1415, c354, c358, c141, c38, c18, c69, c773, c269, c360, c58, c50, c64, c1368, c316, c351, c320, c315, c309, c145, c349, c1414] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c1455 := derived1455 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1415 := derived1415 a h
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c773 := derived773 a h
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c1368 := derived1368 a h
  have h17 : Entails.eval a c316 := h 315 (by decide)
  have h18 : Entails.eval a c351 := h 350 (by decide)
  have h19 : Entails.eval a c320 := h 319 (by decide)
  have h20 : Entails.eval a c315 := h 314 (by decide)
  have h21 : Entails.eval a c309 := h 308 (by decide)
  have h22 : Entails.eval a c145 := h 144 (by decide)
  have h23 : Entails.eval a c349 := h 348 (by decide)
  have h24 : Entails.eval a c1414 := derived1414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1303, some c38, some c18, some c69, some c773, some c269, some c360, some c42, some c58, some c50, some c64, some c233, some c316, some c250, some c320, some c349, some c283, some c303, some c315, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 57) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c1303, c38, c18, c69, c773, c269, c360, c42, c58, c50, c64, c233, c316, c250, c320, c349, c283, c303, c315] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c1303 := derived1303 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c773 := derived773 a h
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c283 := h 282 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨38, by decide⟩, false), (⟨20, by decide⟩, false), (⟨34, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c261, some c250, some c343, some c303, some c46, some c316, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 57) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c261, c250, c343, c303, c46, c316] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c261 := h 260 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨38, by decide⟩, false), (⟨31, by decide⟩, false), (⟨37, by decide⟩, false), (⟨20, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c320, some c1458, some c98, some c50, some c346, some c341, some c221, some c304, some c281, some c318, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 57) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c356, c320, c1458, c98, c50, c346, c341, c221, c304, c281, c318] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c346 := h 345 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c221 := h 220 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1303, some c1455, some c30, some c19, some c1456, some c1457, some c356, some c233, some c269, some c29, some c1092, some c360, some c43, some c76, some c211, some c1459, some c47, some c58, some c341, some c221, some c46, some c281, some c318, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 57) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c631, c1303, c1455, c30, c19, c1456, c1457, c356, c233, c269, c29, c1092, c360, c43, c76, c211, c1459, c47, c58, c341, c221, c46, c281, c318] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1455 := derived1455 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c1456 := derived1456 a h
  have h6 : Entails.eval a c1457 := derived1457 a h
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c1092 := derived1092 a h
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c1459 := derived1459 a h
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c341 := h 340 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c281 := h 280 (by decide)
  have h23 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c356, some c29, some c1092, some c265, some c360, some c28, some c72, some c111, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 57) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1077, c356, c29, c1092, c265, c360, c28, c72, c111] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c1092 := derived1092 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c356, some c1303, some c233, some c1461, some c269, some c36, some c1092, some c265, some c360, some c34, some c72, some c111, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 57) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c1077, c356, c1303, c233, c1461, c269, c36, c1092, c265, c360, c34, c72, c111] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c1461 := derived1461 a h
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c1092 := derived1092 a h
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c358, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 57) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1415, c358] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1464 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c231, some c233, some c268, some c271, some c28, some c235, some c111, some c40, some c72, some c1221, some c217, some c353, some c143, some c163, some c204, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 57) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c231, c233, c268, c271, c28, c235, c111, c40, c72, c1221, c217, c353, c143, c163, c204] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c231 := h 230 (by decide)
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c271 := h 270 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1221 := derived1221 a h
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c163 := h 162 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1442, some c1448, some c107, some c1303, some c1460, some c1077, some c1463, some c1462, some c231, some c1464, some c357, some c22, some c76, some c42, some c210, some c141, some c353, some c235, some c74, some c1092, some c271, some c111, some c32, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 57) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c631, c1442, c1448, c107, c1303, c1460, c1077, c1463, c1462, c231, c1464, c357, c22, c76, c42, c210, c141, c353, c235, c74, c1092, c271, c111, c32] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1442 := derived1442 a h
  have h2 : Entails.eval a c1448 := derived1448 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c1460 := derived1460 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c1463 := derived1463 a h
  have h8 : Entails.eval a c1462 := derived1462 a h
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c1464 := derived1464 a h
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c235 := h 234 (by decide)
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c1092 := derived1092 a h
  have h21 : Entails.eval a c271 := h 270 (by decide)
  have h22 : Entails.eval a c111 := h 110 (by decide)
  have h23 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c1167, some c38, some c46, some c256, some c341, some c99, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 57) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c24, c1167, c38, c46, c256, c341, c99] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c1167 := derived1167 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨30, by decide⟩, true), (⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c144, some c280, some c13, some c320, some c134, some c158, some c208, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 57) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c144, c280, c13, c320, c134, c158, c208] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c220, some c316, some c56, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 57) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c220, c316, c56] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c220 := h 219 (by decide)
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨39, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1468, some c280, some c1467, some c320, some c318, some c56, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 57) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c1468, c280, c1467, c320, c318, c56] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c1468 := derived1468 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c1467 := derived1467 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1465, some c106, some c631, some c1442, some c24, some c44, some c266, some c267, some c1466, some c18, some c29, some c1274, some c356, some c105, some c75, some c28, some c360, some c1431, some c119, some c232, some c1469, some c47, some c346, some c341, some c96, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 57) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1465, c106, c631, c1442, c24, c44, c266, c267, c1466, c18, c29, c1274, c356, c105, c75, c28, c360, c1431, c119, c232, c1469, c47, c346, c341, c96] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1465 := derived1465 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1442 := derived1442 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c1466 := derived1466 a h
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c1274 := derived1274 a h
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c1431 := derived1431 a h
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c232 := h 231 (by decide)
  have h20 : Entails.eval a c1469 := derived1469 a h
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c346 := h 345 (by decide)
  have h23 : Entails.eval a c341 := h 340 (by decide)
  have h24 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨38, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c266, some c267, some c1275, some c118, some c236, some c1289, some c13, some c355, some c163, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 57) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c631, c266, c267, c1275, c118, c236, c1289, c13, c355, c163] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c1289 := derived1289 a h
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c43, some c219, some c47, some c259, some c341, some c97, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 57) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c23, c43, c219, c47, c259, c341, c97] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c356, some c358, some c1471, some c31, some c1472, some c355, some c141, some c163, some c1289, some c13, some c118, some c146, some c210, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 57) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c631, c356, c358, c1471, c31, c1472, c355, c141, c163, c1289, c13, c118, c146, c210] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c1471 := derived1471 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c1472 := derived1472 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c1289 := derived1289 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨39, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c52, some c256, some c352, some c97, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 57) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c216, c52, c256, c352, c97] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1473, some c38, some c18, some c69, some c1474, some c31, some c1450, some c47, some c347, some c253, some c97, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 57) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c1473, c38, c18, c69, c1474, c31, c1450, c47, c347, c253, c97] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c1473 := derived1473 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c1474 := derived1474 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c1450 := derived1450 a h
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1465, some c106, some c1442, some c1470, some c1475, some c105, some c631, some c356, some c358, some c1471, some c789, some c31, some c1431, some c525, some c41, some c355, some c209, some c141, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 57) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1465, c106, c1442, c1470, c1475, c105, c631, c356, c358, c1471, c789, c31, c1431, c525, c41, c355, c209, c141] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1465 := derived1465 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1442 := derived1442 a h
  have h3 : Entails.eval a c1470 := derived1470 a h
  have h4 : Entails.eval a c1475 := derived1475 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c1471 := derived1471 a h
  have h10 : Entails.eval a c789 := derived789 a h
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c1431 := derived1431 a h
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c216, some c232, some c59, some c63, some c214, some c320, some c280, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 57) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c267, c216, c232, c59, c63, c214, c320, c280] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1465, some c106, some c631, some c1442, some c1470, some c1475, some c105, some c1476, some c38, some c18, some c68, some c360, some c359, some c1477, some c789, some c31, some c1431, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 57) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c1465, c106, c631, c1442, c1470, c1475, c105, c1476, c38, c18, c68, c360, c359, c1477, c789, c31, c1431] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c1465 := derived1465 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1442 := derived1442 a h
  have h4 : Entails.eval a c1470 := derived1470 a h
  have h5 : Entails.eval a c1475 := derived1475 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1476 := derived1476 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c1477 := derived1477 a h
  have h14 : Entails.eval a c789 := derived789 a h
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c1431 := derived1431 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c43, some c219, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 57) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c23, c43, c219] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨33, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c13, some c204, some c207, some c757, some c638, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 57) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c163, c13, c204, c207, c757, c638] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c757 := derived757 a h
  have h5 : Entails.eval a c638 := derived638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1481 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1479, some c219, some c51, some c352, some c259, some c99, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1481 : lratChecker f1481 p1481 = .success := by decide +kernel
theorem unsat1481 : Unsatisfiable (PosFin 57) f1481 := by
  apply lratCheckerSound f1481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1481
  · intro a ha; simp [p1481] at ha; subst a; trivial
  · exact checked1481
theorem derived1481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1481 := by
  apply localUnsat_implies_entails f1481 [c1479, c219, c51, c352, c259, c99] c1481 unsat1481 (by rfl) a
  have h0 : Entails.eval a c1479 := derived1479 a h
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1482 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1450, some c1479, some c355, some c141, some c1481, some c29, some c213, some c46, some c57, some c344, some c315, some c52, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1482 : lratChecker f1482 p1482 = .success := by decide +kernel
theorem unsat1482 : Unsatisfiable (PosFin 57) f1482 := by
  apply lratCheckerSound f1482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1482
  · intro a ha; simp [p1482] at ha; subst a; trivial
  · exact checked1482
theorem derived1482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1482 := by
  apply localUnsat_implies_entails f1482 [c1450, c1479, c355, c141, c1481, c29, c213, c46, c57, c344, c315, c52] c1482 unsat1482 (by rfl) a
  have h0 : Entails.eval a c1450 := derived1450 a h
  have h1 : Entails.eval a c1479 := derived1479 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c1481 := derived1481 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1483 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨38, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c525, some c218, some c56, some c63, some c41, some c49, some c316, some c1278, some c348, some c249, some c303, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1483 : lratChecker f1483 p1483 = .success := by decide +kernel
theorem unsat1483 : Unsatisfiable (PosFin 57) f1483 := by
  apply lratCheckerSound f1483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1483
  · intro a ha; simp [p1483] at ha; subst a; trivial
  · exact checked1483
theorem derived1483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1483 := by
  apply localUnsat_implies_entails f1483 [c525, c218, c56, c63, c41, c49, c316, c1278, c348, c249, c303] c1483 unsat1483 (by rfl) a
  have h0 : Entails.eval a c525 := derived525 a h
  have h1 : Entails.eval a c218 := h 217 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1483

end CochromaticTwenty.Certificates.B16_4_2
