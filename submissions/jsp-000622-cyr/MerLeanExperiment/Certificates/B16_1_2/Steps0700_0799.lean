import MerLeanExperiment.Certificates.B16_1_2.Steps0600_0699

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1094 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, true), (⟨55, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c215, some c344, some c79, some c162, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 57) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c35, c215, c344, c79, c162] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨55, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c307, some c386, some c18, some c123, some c89, some c1094, some c255, some c567, some c37, some c33, some c289, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 57) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c1, c307, c386, c18, c123, c89, c1094, c255, c567, c37, c33, c289] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c1094 := derived1094 a h
  have h7 : Entails.eval a c255 := h 254 (by decide)
  have h8 : Entails.eval a c567 := derived567 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1096 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c255, some c135, some c46, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 57) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c255, c135, c46] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c215, some c63, some c62, some c770, some c306, some c283, some c110, some c352, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c307, c215, c63, c62, c770, c306, c283, c110, c352] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c770 := derived770 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c1093, some c307, some c386, some c1095, some c208, some c13, some c1077, some c123, some c17, some c121, some c1078, some c1096, some c35, some c215, some c344, some c82, some c161, some c145, some c74, some c163, some c1097, some c327, some c212, some c133, some c137, some c50, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c1, c1093, c307, c386, c1095, c208, c13, c1077, c123, c17, c121, c1078, c1096, c35, c215, c344, c82, c161, c145, c74, c163, c1097, c327, c212, c133, c137, c50] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c1093 := derived1093 a h
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c386 := h 385 (by decide)
  have h4 : Entails.eval a c1095 := derived1095 a h
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c1077 := derived1077 a h
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c1078 := derived1078 a h
  have h12 : Entails.eval a c1096 := derived1096 a h
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c215 := h 214 (by decide)
  have h15 : Entails.eval a c344 := h 343 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c145 := h 144 (by decide)
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c163 := h 162 (by decide)
  have h21 : Entails.eval a c1097 := derived1097 a h
  have h22 : Entails.eval a c327 := h 326 (by decide)
  have h23 : Entails.eval a c212 := h 211 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  have h25 : Entails.eval a c137 := h 136 (by decide)
  have h26 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c19, some c1, some c18, some c208, some c204, some c17, some c192, some c1083, some c389, some c1080, some c111, some c122, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 57) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c1057, c19, c1, c18, c208, c204, c17, c192, c1083, c389, c1080, c111, c122] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c1083 := derived1083 a h
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c1080 := derived1080 a h
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c19, some c208, some c204, some c199, some c13, some c17, some c124, some c35, some c64, some c135, some c140, some c36, some c216, some c223, some c76, some c324, some c142, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 57) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c1057, c19, c208, c204, c199, c13, c17, c124, c35, c64, c135, c140, c36, c216, c223, c76, c324, c142] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c306, some c290, some c90, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 57) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c306, c290, c90] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c306 := h 305 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨20, by decide⟩, false), (⟨41, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1101, some c6, some c34, some c137, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 57) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c1101, c6, c34, c137] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c1101 := derived1101 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c16, some c36, some c140, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 57) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1057, c16, c36, c140] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c1093, some c386, some c307, some c1098, some c19, some c1099, some c1100, some c1094, some c255, some c37, some c47, some c1102, some c1103, some c122, some c17, some c45, some c130, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 57) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c1, c1093, c386, c307, c1098, c19, c1099, c1100, c1094, c255, c37, c47, c1102, c1103, c122, c17, c45, c130] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c1093 := derived1093 a h
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c1098 := derived1098 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c1099 := derived1099 a h
  have h7 : Entails.eval a c1100 := derived1100 a h
  have h8 : Entails.eval a c1094 := derived1094 a h
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c1102 := derived1102 a h
  have h13 : Entails.eval a c1103 := derived1103 a h
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c1104, some c1, some c147, some c7, some c84, some c148, some c216, some c206, some c132, some c160, some c45, some c30, some c306, some c271, some c325, some c200, some c156, some c204, some c18, some c1094, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 57) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c17, c1104, c1, c147, c7, c84, c148, c216, c206, c132, c160, c45, c30, c306, c271, c325, c200, c156, c204, c18, c1094] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c1104 := derived1104 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c206 := h 205 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c204 := h 203 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨15, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c903, some c254, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 57) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c200, c903, c254] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c903 := derived903 a h
  have h2 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c15, some c124, some c17, some c253, some c89, some c108, some c1070, some c1106, some c206, some c205, some c195, some c197, some c389, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 57) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c1057, c15, c124, c17, c253, c89, c108, c1070, c1106, c206, c205, c195, c197, c389] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1070 := derived1070 a h
  have h8 : Entails.eval a c1106 := derived1106 a h
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c789, some c148, some c83, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 57) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c206, c789, c148, c83] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c789 := derived789 a h
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c1105, some c321, some c1104, some c307, some c15, some c124, some c60, some c33, some c5, some c17, some c1107, some c45, some c1089, some c1090, some c1108, some c200, some c1073, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 57) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1, c1105, c321, c1104, c307, c15, c124, c60, c33, c5, c17, c1107, c45, c1089, c1090, c1108, c200, c1073] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c1105 := derived1105 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c1107 := derived1107 a h
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c1089 := derived1089 a h
  have h14 : Entails.eval a c1090 := derived1090 a h
  have h15 : Entails.eval a c1108 := derived1108 a h
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c1073 := derived1073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c1073, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 57) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c200, c1073] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c1073 := derived1073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1111 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1104, some c1, some c1105, some c307, some c15, some c321, some c17, some c124, some c5, some c60, some c1109, some c207, some c19, some c196, some c1110, some c206, some c1108, some c157, some c45, some c1031, some c310, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 57) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1104, c1, c1105, c307, c15, c321, c17, c124, c5, c60, c1109, c207, c19, c196, c1110, c206, c1108, c157, c45, c1031, c310] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1104 := derived1104 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1105 := derived1105 a h
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c1109 := derived1109 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c1110 := derived1110 a h
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c1108 := derived1108 a h
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c1031 := derived1031 a h
  have h20 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c157, some c324, some c155, some c325, some c1058, some c148, some c8, some c19, some c9, some c1, some c121, some c1111, some c83, some c1108, some c1105, some c31, some c214, some c45, some c321, some c134, some c270, some c227, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 57) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c206, c157, c324, c155, c325, c1058, c148, c8, c19, c9, c1, c121, c1111, c83, c1108, c1105, c31, c214, c45, c321, c134, c270, c227] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c155 := h 154 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c1111 := derived1111 a h
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c1108 := derived1108 a h
  have h15 : Entails.eval a c1105 := derived1105 a h
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c321 := h 320 (by decide)
  have h20 : Entails.eval a c134 := h 133 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  have h22 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c206, some c197, some c157, some c19, some c9, some c325, some c324, some c310, some c1112, some c34, some c62, some c131, some c120, some c123, some c45, some c1031, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 57) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c1057, c206, c197, c157, c19, c9, c325, c324, c310, c1112, c34, c62, c131, c120, c123, c45, c1031] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c1112 := derived1112 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c131 := h 130 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c1031 := derived1031 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨26, by decide⟩, true), (⟨40, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c210, some c76, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c30, c210, c76] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c9, some c1, some c42, some c34, some c179, some c1101, some c93, some c120, some c18, some c50, some c129, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c131, c9, c1, c42, c34, c179, c1101, c93, c120, c18, c50, c129] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c1101 := derived1101 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c9, some c1, some c206, some c8, some c148, some c1113, some c1114, some c1115, some c121, some c1111, some c83, some c1105, some c1025, some c821, some c716, some c307, some c93, some c306, some c291, some c377, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c19, c9, c1, c206, c8, c148, c1113, c1114, c1115, c121, c1111, c83, c1105, c1025, c821, c716, c307, c93, c306, c291, c377] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c1113 := derived1113 a h
  have h7 : Entails.eval a c1114 := derived1114 a h
  have h8 : Entails.eval a c1115 := derived1115 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c1111 := derived1111 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c1105 := derived1105 a h
  have h13 : Entails.eval a c1025 := derived1025 a h
  have h14 : Entails.eval a c821 := derived821 a h
  have h15 : Entails.eval a c716 := derived716 a h
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c291 := h 290 (by decide)
  have h20 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c19, some c9, some c1104, some c1, some c1116, some c1073, some c1110, some c14, some c307, some c121, some c156, some c160, some c1105, some c325, some c16, some c36, some c30, some c132, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1057, c19, c9, c1104, c1, c1116, c1073, c1110, c14, c307, c121, c156, c160, c1105, c325, c16, c36, c30, c132] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1116 := derived1116 a h
  have h6 : Entails.eval a c1073 := derived1073 a h
  have h7 : Entails.eval a c1110 := derived1110 a h
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c160 := h 159 (by decide)
  have h13 : Entails.eval a c1105 := derived1105 a h
  have h14 : Entails.eval a c325 := h 324 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c30 := h 29 (by decide)
  have h18 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c9, some c1, some c1073, some c14, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c19, c9, c1, c1073, c14] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1073 := derived1073 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c16, some c92, some c187, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c1057, c16, c92, c187] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨48, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c9, some c1, some c322, some c301, some c1104, some c374, some c153, some c1080, some c307, some c193, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c1057, c9, c1, c322, c301, c1104, c374, c153, c1080, c307, c193] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c1104 := derived1104 a h
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c1080 := derived1080 a h
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨46, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c17, some c121, some c1118, some c1119, some c120, some c18, some c1, some c142, some c74, some c144, some c76, some c169, some c187, some c1120, some c34, some c62, some c139, some c327, some c216, some c152, some c323, some c208, some c153, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c19, c17, c121, c1118, c1119, c120, c18, c1, c142, c74, c144, c76, c169, c187, c1120, c34, c62, c139, c327, c216, c152, c323, c208, c153] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c1118 := derived1118 a h
  have h4 : Entails.eval a c1119 := derived1119 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c187 := h 186 (by decide)
  have h14 : Entails.eval a c1120 := derived1120 a h
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c327 := h 326 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c152 := h 151 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true), (⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c164, some c342, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c192, c164, c342] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c164 := h 163 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨51, by decide⟩, false), (⟨26, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c17, some c120, some c18, some c9, some c1, some c324, some c309, some c144, some c74, some c161, some c1122, some c208, some c156, some c193, some c307, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c19, c17, c120, c18, c9, c1, c324, c309, c144, c74, c161, c1122, c208, c156, c193, c307] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c1122 := derived1122 a h
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c90, some c19, some c9, some c1, some c17, some c1121, some c120, some c110, some c1123, some c62, some c326, some c325, some c1104, some c156, some c307, some c196, some c193, some c1080, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c90, c19, c9, c1, c17, c1121, c120, c110, c1123, c62, c326, c325, c1104, c156, c307, c196, c193, c1080] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1121 := derived1121 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c1123 := derived1123 a h
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c1104 := derived1104 a h
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c1080 := derived1080 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c19, some c9, some c1, some c1124, some c1117, some c206, some c1115, some c1024, some c322, some c323, some c197, some c38, some c120, some c18, some c110, some c62, some c392, some c313, some c1077, some c156, some c208, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1057, c19, c9, c1, c1124, c1117, c206, c1115, c1024, c322, c323, c197, c38, c120, c18, c110, c62, c392, c313, c1077, c156, c208] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c1117 := derived1117 a h
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c1115 := derived1115 a h
  have h8 : Entails.eval a c1024 := derived1024 a h
  have h9 : Entails.eval a c322 := h 321 (by decide)
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c392 := h 391 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c1077 := derived1077 a h
  have h20 : Entails.eval a c156 := h 155 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c147, some c324, some c156, some c207, some c137, some c212, some c74, some c161, some c164, some c358, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c153, c147, c324, c156, c207, c137, c212, c74, c161, c164, c358] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c120, some c18, some c121, some c9, some c1, some c306, some c34, some c254, some c37, some c1126, some c307, some c291, some c193, some c390, some c373, some c196, some c181, some c185, some c98, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c17, c120, c18, c121, c9, c1, c306, c34, c254, c37, c1126, c307, c291, c193, c390, c373, c196, c181, c185, c98] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c1126 := derived1126 a h
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c390 := h 389 (by decide)
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c196 := h 195 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨49, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c321, some c193, some c152, some c309, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c307, c321, c193, c152, c309] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1128, some c153, some c309, some c193, some c192, some c386, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c1128, c153, c309, c193, c192, c386] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c1128 := derived1128 a h
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c386 := h 385 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c120, some c18, some c121, some c9, some c1, some c1127, some c1124, some c110, some c207, some c1129, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c17, c120, c18, c121, c9, c1, c1127, c1124, c110, c207, c1129] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1127 := derived1127 a h
  have h7 : Entails.eval a c1124 := derived1124 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c1129 := derived1129 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c18, some c9, some c1, some c306, some c322, some c90, some c1124, some c110, some c185, some c207, some c1058, some c187, some c374, some c1080, some c392, some c192, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c1057, c18, c9, c1, c306, c322, c90, c1124, c110, c185, c207, c1058, c187, c374, c1080, c392, c192] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c1124 := derived1124 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c1058 := derived1058 a h
  have h12 : Entails.eval a c187 := h 186 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c1080 := derived1080 a h
  have h15 : Entails.eval a c392 := h 391 (by decide)
  have h16 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c9, some c1129, some c1104, some c323, some c322, some c68, some c786, some c835, some c152, some c145, some c324, some c82, some c80, some c284, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c1, c9, c1129, c1104, c323, c322, c68, c786, c835, c152, c145, c324, c82, c80, c284] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1129 := derived1129 a h
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c786 := derived786 a h
  have h8 : Entails.eval a c835 := derived835 a h
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c9, some c1129, some c1104, some c322, some c34, some c6, some c137, some c185, some c40, some c1132, some c192, some c199, some c1080, some c187, some c374, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c1057, c1, c9, c1129, c1104, c322, c34, c6, c137, c185, c40, c1132, c192, c199, c1080, c187, c374] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1104 := derived1104 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c1132 := derived1132 a h
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c1080 := derived1080 a h
  have h15 : Entails.eval a c187 := h 186 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c1, some c9, some c1129, some c1104, some c322, some c34, some c6, some c137, some c1133, some c90, some c98, some c254, some c183, some c181, some c46, some c248, some c135, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c18, c1, c9, c1129, c1104, c322, c34, c6, c137, c1133, c90, c98, c254, c183, c181, c46, c248, c135] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1104 := derived1104 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c1133 := derived1133 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c19, some c1123, some c142, some c152, some c74, some c327, some c144, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c17, c19, c1123, c142, c152, c74, c327, c144] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1123 := derived1123 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1135, some c1, some c9, some c1129, some c1104, some c323, some c322, some c17, some c6, some c34, some c68, some c137, some c1134, some c120, some c124, some c32, some c5, some c327, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c1135, c1, c9, c1129, c1104, c323, c322, c17, c6, c34, c68, c137, c1134, c120, c124, c32, c5, c327] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c1135 := derived1135 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1104 := derived1104 a h
  have h5 : Entails.eval a c323 := h 322 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c1134 := derived1134 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c17, some c1136, some c121, some c122, some c113, some c389, some c392, some c192, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c1057, c17, c1136, c121, c122, c113, c389, c392, c192] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c1136 := derived1136 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c92, some c16, some c9, some c192, some c386, some c786, some c193, some c152, some c1104, some c188, some c296, some c370, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c1057, c92, c16, c9, c192, c386, c786, c193, c152, c1104, c188, c296, c370] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c386 := h 385 (by decide)
  have h6 : Entails.eval a c786 := derived786 a h
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c1104 := derived1104 a h
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨48, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c386, some c786, some c5, some c124, some c15, some c91, some c188, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c9, c386, c786, c5, c124, c15, c91, c188] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c17, some c121, some c122, some c16, some c92, some c113, some c111, some c1138, some c390, some c1139, some c198, some c13, some c1119, some c124, some c371, some c375, some c384, some c385, some c100, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1057, c17, c121, c122, c16, c92, c113, c111, c1138, c390, c1139, c198, c13, c1119, c124, c371, c375, c384, c385, c100] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1138 := derived1138 a h
  have h9 : Entails.eval a c390 := h 389 (by decide)
  have h10 : Entails.eval a c1139 := derived1139 a h
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c1119 := derived1119 a h
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c375 := h 374 (by decide)
  have h17 : Entails.eval a c384 := h 383 (by decide)
  have h18 : Entails.eval a c385 := h 384 (by decide)
  have h19 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c1, some c91, some c43, some c307, some c255, some c7, some c37, some c1104, some c292, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c9, c1, c91, c43, c307, c255, c7, c37, c1104, c292] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c1104 := derived1104 a h
  have h9 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c9, some c1, some c1104, some c1099, some c322, some c1077, some c17, some c1137, some c121, some c62, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c18, c9, c1, c1104, c1099, c322, c1077, c17, c1137, c121, c62] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c1099 := derived1099 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1137 := derived1137 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c111, some c1142, some c199, some c9, some c1, some c322, some c323, some c160, some c206, some c17, some c192, some c1129, some c389, some c62, some c113, some c121, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1057, c111, c1142, c199, c9, c1, c322, c323, c160, c206, c17, c192, c1129, c389, c62, c113, c121] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c1142 := derived1142 a h
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c1129 := derived1129 a h
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c18, some c111, some c1143, some c63, some c1137, some c1117, some c204, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1057, c18, c111, c1143, c63, c1137, c1117, c204] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1143 := derived1143 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1117 := derived1117 a h
  have h7 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c13, some c199, some c9, some c1, some c92, some c1144, some c124, some c1141, some c188, some c15, some c7, some c307, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1057, c13, c199, c9, c1, c92, c1144, c124, c1141, c188, c15, c7, c307] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c1144 := derived1144 a h
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c1141 := derived1141 a h
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c7, some c307, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c15, c7, c307] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c1, some c123, some c124, some c19, some c1146, some c1104, some c322, some c323, some c68, some c64, some c122, some c17, some c61, some c938, some c324, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c9, c1, c123, c124, c19, c1146, c1104, c322, c323, c68, c64, c122, c17, c61, c938, c324] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c1146 := derived1146 a h
  have h6 : Entails.eval a c1104 := derived1104 a h
  have h7 : Entails.eval a c322 := h 321 (by decide)
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c938 := derived938 a h
  have h15 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c9, some c1146, some c1059, some c91, some c918, some c1066, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1, c9, c1146, c1059, c91, c918, c1066] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1146 := derived1146 a h
  have h3 : Entails.eval a c1059 := derived1059 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c918 := derived918 a h
  have h6 : Entails.eval a c1066 := derived1066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c9, some c1146, some c1104, some c323, some c324, some c64, some c1148, some c386, some c1095, some c13, some c208, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1, c9, c1146, c1104, c323, c324, c64, c1148, c386, c1095, c13, c208] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1146 := derived1146 a h
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c1148 := derived1148 a h
  have h8 : Entails.eval a c386 := h 385 (by decide)
  have h9 : Entails.eval a c1095 := derived1095 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c386, some c1095, some c13, some c208, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c9, c386, c1095, c13, c208] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c1095 := derived1095 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c9, some c1, some c1146, some c1104, some c322, some c323, some c68, some c122, some c17, some c61, some c1149, some c938, some c19, some c1150, some c91, some c918, some c786, some c1066, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1147, c9, c1, c1146, c1104, c322, c323, c68, c122, c17, c61, c1149, c938, c19, c1150, c91, c918, c786, c1066] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1146 := derived1146 a h
  have h4 : Entails.eval a c1104 := derived1104 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c1149 := derived1149 a h
  have h12 : Entails.eval a c938 := derived938 a h
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c1150 := derived1150 a h
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c918 := derived918 a h
  have h17 : Entails.eval a c786 := derived786 a h
  have h18 : Entails.eval a c1066 := derived1066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c1, some c9, some c1104, some c323, some c322, some c786, some c5, some c33, some c60, some c208, some c138, some c253, some c228, some c45, some c131, some c273, some c514, some c224, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c17, c1, c9, c1104, c323, c322, c786, c5, c33, c60, c208, c138, c253, c228, c45, c131, c273, c514, c224] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c786 := derived786 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c253 := h 252 (by decide)
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c273 := h 272 (by decide)
  have h17 : Entails.eval a c514 := derived514 a h
  have h18 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c9, some c1104, some c322, some c120, some c1150, some c17, some c1152, some c13, some c89, some c108, some c208, some c186, some c1075, some c206, some c6, some c146, some c1071, some c81, some c1079, some c184, some c1073, some c163, some c377, some c330, some c382, some c93, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1, c9, c1104, c322, c120, c1150, c17, c1152, c13, c89, c108, c208, c186, c1075, c206, c6, c146, c1071, c81, c1079, c184, c1073, c163, c377, c330, c382, c93] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1104 := derived1104 a h
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c1150 := derived1150 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c1152 := derived1152 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c1075 := derived1075 a h
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c1071 := derived1071 a h
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c1079 := derived1079 a h
  have h20 : Entails.eval a c184 := h 183 (by decide)
  have h21 : Entails.eval a c1073 := derived1073 a h
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c377 := h 376 (by decide)
  have h24 : Entails.eval a c330 := h 329 (by decide)
  have h25 : Entails.eval a c382 := h 381 (by decide)
  have h26 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c89, some c1070, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c13, c89, c1070] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c1070 := derived1070 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c9, some c1, some c1104, some c322, some c1153, some c1154, some c786, some c1152, some c66, some c122, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1147, c9, c1, c1104, c322, c1153, c1154, c786, c1152, c66, c122] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1104 := derived1104 a h
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c1153 := derived1153 a h
  have h6 : Entails.eval a c1154 := derived1154 a h
  have h7 : Entails.eval a c786 := derived786 a h
  have h8 : Entails.eval a c1152 := derived1152 a h
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c1154, some c786, some c5, some c33, some c253, some c1089, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c9, c1154, c786, c5, c33, c253, c1089] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c1154 := derived1154 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c1089 := derived1089 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1156, some c120, some c9, some c786, some c33, some c253, some c45, some c17, some c1155, some c1, some c66, some c821, some c1111, some c81, some c83, some c323, some c160, some c206, some c205, some c169, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 57) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c1147, c1156, c120, c9, c786, c33, c253, c45, c17, c1155, c1, c66, c821, c1111, c81, c83, c323, c160, c206, c205, c169] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c786 := derived786 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c1155 := derived1155 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c821 := derived821 a h
  have h13 : Entails.eval a c1111 := derived1111 a h
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1156, some c120, some c9, some c1, some c786, some c33, some c253, some c37, some c1157, some c322, some c1101, some c1111, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 57) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c1147, c1156, c120, c9, c1, c786, c33, c253, c37, c1157, c322, c1101, c1111] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c786 := derived786 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c1157 := derived1157 a h
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c1101 := derived1101 a h
  have h12 : Entails.eval a c1111 := derived1111 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1158, some c1147, some c1156, some c120, some c9, some c1, some c306, some c322, some c114, some c1111, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 57) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c1158, c1147, c1156, c120, c9, c1, c306, c322, c114, c1111] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c1158 := derived1158 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1156 := derived1156 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c322 := h 321 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c1111 := derived1111 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1159, some c1147, some c1156, some c1158, some c492, some c120, some c17, some c1155, some c9, some c1, some c60, some c66, some c1111, some c323, some c160, some c206, some c205, some c197, some c156, some c310, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 57) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1057, c1159, c1147, c1156, c1158, c492, c120, c17, c1155, c9, c1, c60, c66, c1111, c323, c160, c206, c205, c197, c156, c310] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1159 := derived1159 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c1156 := derived1156 a h
  have h4 : Entails.eval a c1158 := derived1158 a h
  have h5 : Entails.eval a c492 := derived492 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1155 := derived1155 a h
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c1111 := derived1111 a h
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c205 := h 204 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c1147, some c1151, some c1155, some c1156, some c120, some c17, some c1158, some c13, some c89, some c492, some c1159, some c1160, some c321, some c289, some c160, some c147, some c93, some c206, some c205, some c84, some c79, some c179, some c197, some c167, some c389, some c390, some c182, some c371, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 57) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c1057, c1, c1147, c1151, c1155, c1156, c120, c17, c1158, c13, c89, c492, c1159, c1160, c321, c289, c160, c147, c93, c206, c205, c84, c79, c179, c197, c167, c389, c390, c182, c371] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c1151 := derived1151 a h
  have h4 : Entails.eval a c1155 := derived1155 a h
  have h5 : Entails.eval a c1156 := derived1156 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1158 := derived1158 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c492 := derived492 a h
  have h12 : Entails.eval a c1159 := derived1159 a h
  have h13 : Entails.eval a c1160 := derived1160 a h
  have h14 : Entails.eval a c321 := h 320 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c93 := h 92 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c79 := h 78 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  have h24 : Entails.eval a c197 := h 196 (by decide)
  have h25 : Entails.eval a c167 := h 166 (by decide)
  have h26 : Entails.eval a c389 := h 388 (by decide)
  have h27 : Entails.eval a c390 := h 389 (by decide)
  have h28 : Entails.eval a c182 := h 181 (by decide)
  have h29 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c1, some c786, some c13, some c89, some c182, some c289, some c94, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 57) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c18, c1, c786, c13, c89, c182, c289, c94] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c9, some c1162, some c5, some c33, some c134, some c46, some c39, some c253, some c182, some c89, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 57) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c18, c9, c1162, c5, c33, c134, c46, c39, c253, c182, c89] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1162 := derived1162 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c253 := h 252 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c9, some c1118, some c50, some c1125, some c254, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 57) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c46, c9, c1118, c50, c1125, c254] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c39, some c18, some c1, some c207, some c182, some c19, some c376, some c1164, some c121, some c17, some c177, some c1117, some c93, some c292, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 57) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c1057, c39, c18, c1, c207, c182, c19, c376, c1164, c121, c17, c177, c1117, c93, c292] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c1164 := derived1164 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  have h12 : Entails.eval a c1117 := derived1117 a h
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c1, some c204, some c1077, some c19, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 57) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c9, c1, c204, c1077, c19] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c31, some c18, some c9, some c1165, some c1145, some c1166, some c17, some c1137, some c122, some c110, some c50, some c254, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 57) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c46, c31, c18, c9, c1165, c1145, c1166, c17, c1137, c122, c110, c50, c254] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1165 := derived1165 a h
  have h5 : Entails.eval a c1145 := derived1145 a h
  have h6 : Entails.eval a c1166 := derived1166 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1137 := derived1137 a h
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c31, some c9, some c1137, some c1140, some c50, some c110, some c254, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 57) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c46, c31, c9, c1137, c1140, c50, c110, c254] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1137 := derived1137 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c163, some c80, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 57) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c19, c163, c80] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1163, some c18, some c9, some c46, some c1167, some c253, some c213, some c342, some c1169, some c204, some c207, some c1168, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 57) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c1163, c18, c9, c46, c1167, c253, c213, c342, c1169, c204, c207, c1168] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c1163 := derived1163 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c1167 := derived1167 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c1169 := derived1169 a h
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c1168 := derived1168 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c121, some c212, some c325, some c324, some c62, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 57) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c80, c121, c212, c325, c324, c62] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c207, some c133, some c145, some c152, some c1171, some c1085, some c32, some c122, some c325, some c324, some c62, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 57) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c207, c133, c145, c152, c1171, c1085, c32, c122, c325, c324, c62] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c1171 := derived1171 a h
  have h5 : Entails.eval a c1085 := derived1085 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c1170, some c1163, some c18, some c9, some c1, some c1172, some c19, some c121, some c1124, some c1118, some c306, some c62, some c1130, some c208, some c145, some c342, some c1169, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 57) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c17, c1170, c1163, c18, c9, c1, c1172, c19, c121, c1124, c1118, c306, c62, c1130, c208, c145, c342, c1169] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c1170 := derived1170 a h
  have h2 : Entails.eval a c1163 := derived1163 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1172 := derived1172 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c1124 := derived1124 a h
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c1130 := derived1130 a h
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c1169 := derived1169 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1173, some c17, some c1163, some c18, some c9, some c1, some c19, some c121, some c1124, some c1118, some c306, some c34, some c62, some c254, some c1130, some c37, some c1104, some c208, some c292, some c145, some c376, some c1169, some c329, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 57) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c1057, c1173, c17, c1163, c18, c9, c1, c19, c121, c1124, c1118, c306, c34, c62, c254, c1130, c37, c1104, c208, c292, c145, c376, c1169, c329] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1173 := derived1173 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c1163 := derived1163 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c1124 := derived1124 a h
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c1130 := derived1130 a h
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c1104 := derived1104 a h
  have h18 : Entails.eval a c208 := h 207 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c145 := h 144 (by decide)
  have h21 : Entails.eval a c376 := h 375 (by decide)
  have h22 : Entails.eval a c1169 := derived1169 a h
  have h23 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1170, some c1163, some c18, some c9, some c1, some c17, some c1173, some c1174, some c207, some c133, some c145, some c1145, some c152, some c192, some c122, some c1171, some c1080, some c1083, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 57) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c1170, c1163, c18, c9, c1, c17, c1173, c1174, c207, c133, c145, c1145, c152, c192, c122, c1171, c1080, c1083] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c1170 := derived1170 a h
  have h1 : Entails.eval a c1163 := derived1163 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1173 := derived1173 a h
  have h7 : Entails.eval a c1174 := derived1174 a h
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c1145 := derived1145 a h
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c1171 := derived1171 a h
  have h16 : Entails.eval a c1080 := derived1080 a h
  have h17 : Entails.eval a c1083 := derived1083 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c18, some c204, some c1117, some c323, some c19, some c1163, some c9, some c1169, some c342, some c358, some c1077, some c147, some c208, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 57) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c1, c18, c204, c1117, c323, c19, c1163, c9, c1169, c342, c358, c1077, c147, c208] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c1163 := derived1163 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c1169 := derived1169 a h
  have h9 : Entails.eval a c342 := h 341 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c1077 := derived1077 a h
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c1170, some c1175, some c1176, some c145, some c213, some c134, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 57) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c18, c1170, c1175, c1176, c145, c213, c134] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c1170 := derived1170 a h
  have h2 : Entails.eval a c1175 := derived1175 a h
  have h3 : Entails.eval a c1176 := derived1176 a h
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1177, some c786, some c1167, some c1, some c321, some c18, some c9, some c204, some c1117, some c129, some c1176, some c1166, some c322, some c208, some c134, some c1146, some c156, some c160, some c147, some c232, some c327, some c206, some c16, some c84, some c169, some c361, some c362, some c282, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 57) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c1057, c1177, c786, c1167, c1, c321, c18, c9, c204, c1117, c129, c1176, c1166, c322, c208, c134, c1146, c156, c160, c147, c232, c327, c206, c16, c84, c169, c361, c362, c282] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1177 := derived1177 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c1167 := derived1167 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c1117 := derived1117 a h
  have h10 : Entails.eval a c129 := h 128 (by decide)
  have h11 : Entails.eval a c1176 := derived1176 a h
  have h12 : Entails.eval a c1166 := derived1166 a h
  have h13 : Entails.eval a c322 := h 321 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c1146 := derived1146 a h
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c232 := h 231 (by decide)
  have h21 : Entails.eval a c327 := h 326 (by decide)
  have h22 : Entails.eval a c206 := h 205 (by decide)
  have h23 : Entails.eval a c16 := h 15 (by decide)
  have h24 : Entails.eval a c84 := h 83 (by decide)
  have h25 : Entails.eval a c169 := h 168 (by decide)
  have h26 : Entails.eval a c361 := h 360 (by decide)
  have h27 : Entails.eval a c362 := h 361 (by decide)
  have h28 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1178, some c17, some c1, some c1177, some c321, some c18, some c208, some c207, some c156, some c153, some c19, some c327, some c325, some c121, some c62, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 57) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1178, c17, c1, c1177, c321, c18, c208, c207, c156, c153, c19, c327, c325, c121, c62] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1178 := derived1178 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1177 := derived1177 a h
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, true), (⟨19, by decide⟩, false), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c275, some c224, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p1180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 57) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c276, c275, c224] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c9, some c1, some c1177, some c786, some c321, some c1167, some c1178, some c17, some c1179, some c1145, some c192, some c122, some c1078, some c1131, some c34, some c62, some c327, some c1137, some c87, some c110, some c298, some c259, some c254, some c1180, some c376, some c244, some c37, some c293, some c292, some c153, some c1104, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 57) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1057, c9, c1, c1177, c786, c321, c1167, c1178, c17, c1179, c1145, c192, c122, c1078, c1131, c34, c62, c327, c1137, c87, c110, c298, c259, c254, c1180, c376, c244, c37, c293, c292, c153, c1104] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1177 := derived1177 a h
  have h4 : Entails.eval a c786 := derived786 a h
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1167 := derived1167 a h
  have h7 : Entails.eval a c1178 := derived1178 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c1179 := derived1179 a h
  have h10 : Entails.eval a c1145 := derived1145 a h
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c1078 := derived1078 a h
  have h14 : Entails.eval a c1131 := derived1131 a h
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c1137 := derived1137 a h
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c298 := h 297 (by decide)
  have h22 : Entails.eval a c259 := h 258 (by decide)
  have h23 : Entails.eval a c254 := h 253 (by decide)
  have h24 : Entails.eval a c1180 := derived1180 a h
  have h25 : Entails.eval a c376 := h 375 (by decide)
  have h26 : Entails.eval a c244 := h 243 (by decide)
  have h27 : Entails.eval a c37 := h 36 (by decide)
  have h28 : Entails.eval a c293 := h 292 (by decide)
  have h29 : Entails.eval a c292 := h 291 (by decide)
  have h30 : Entails.eval a c153 := h 152 (by decide)
  have h31 : Entails.eval a c1104 := derived1104 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1181, some c1161, some c92, some c16, some c9, some c1, some c1146, some c1141, some c188, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 57) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c1057, c1181, c1161, c92, c16, c9, c1, c1146, c1141, c188] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1181 := derived1181 a h
  have h2 : Entails.eval a c1161 := derived1161 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c1146 := derived1146 a h
  have h8 : Entails.eval a c1141 := derived1141 a h
  have h9 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c1181, some c1161, some c16, some c1182, some c124, some c1156, some c115, some c120, some c1153, some c786, some c17, some c67, some c206, some c322, some c323, some c160, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 57) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1057, c1, c1181, c1161, c16, c1182, c124, c1156, c115, c120, c1153, c786, c17, c67, c206, c322, c323, c160] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1181 := derived1181 a h
  have h3 : Entails.eval a c1161 := derived1161 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1182 := derived1182 a h
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c1156 := derived1156 a h
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c1153 := derived1153 a h
  have h11 : Entails.eval a c786 := derived786 a h
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c322 := h 321 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1183, some c117, some c436, some c5, some c33, some c322, some c323, some c160, some c147, some c206, some c71, some c79, some c153, some c162, some c207, some c134, some c156, some c211, some c324, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 57) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1183, c117, c436, c5, c33, c322, c323, c160, c147, c206, c71, c79, c153, c162, c207, c134, c156, c211, c324] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1183 := derived1183 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c211 := h 210 (by decide)
  have h18 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨49, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c327, some c309, some c156, some c628, some c367, some c20, some c298, some c181, some c120, some c41, some c368, some c40, some c264, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 57) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c153, c327, c309, c156, c628, c367, c20, c298, c181, c120, c41, c368, c40, c264] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c628 := derived628 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c298 := h 297 (by decide)
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c161, some c348, some c362, some c90, some c163, some c75, some c207, some c20, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 57) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c161, c348, c362, c90, c163, c75, c207, c20] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c161 := h 160 (by decide)
  have h1 : Entails.eval a c348 := h 347 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨10, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1183, some c119, some c117, some c115, some c1184, some c305, some c189, some c321, some c147, some c71, some c79, some c162, some c92, some c160, some c1119, some c1186, some c733, some c282, some c36, some c1185, some c292, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 57) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1057, c1183, c119, c117, c115, c1184, c305, c189, c321, c147, c71, c79, c162, c92, c160, c1119, c1186, c733, c282, c36, c1185, c292] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1183 := derived1183 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c1184 := derived1184 a h
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c1119 := derived1119 a h
  have h16 : Entails.eval a c1186 := derived1186 a h
  have h17 : Entails.eval a c733 := derived733 a h
  have h18 : Entails.eval a c282 := h 281 (by decide)
  have h19 : Entails.eval a c36 := h 35 (by decide)
  have h20 : Entails.eval a c1185 := derived1185 a h
  have h21 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1183, some c1184, some c321, some c147, some c71, some c79, some c162, some c117, some c119, some c153, some c1187, some c322, some c325, some c65, some c156, some c120, some c207, some c20, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 57) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c1183, c1184, c321, c147, c71, c79, c162, c117, c119, c153, c1187, c322, c325, c65, c156, c120, c207, c20] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c1183 := derived1183 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c1187 := derived1187 a h
  have h11 : Entails.eval a c322 := h 321 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c156 := h 155 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1183, some c119, some c117, some c115, some c1184, some c305, some c321, some c147, some c71, some c79, some c162, some c1188, some c204, some c156, some c191, some c316, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 57) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c1057, c1183, c119, c117, c115, c1184, c305, c321, c147, c71, c79, c162, c1188, c204, c156, c191, c316] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1183 := derived1183 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c1184 := derived1184 a h
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c1188 := derived1188 a h
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c156 := h 155 (by decide)
  have h15 : Entails.eval a c191 := h 190 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨49, by decide⟩, true), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c1183, some c5, some c33, some c67, some c118, some c28, some c206, some c21, some c120, some c24, some c207, some c136, some c190, some c40, some c393, some c184, some c89, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 57) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c15, c1183, c5, c33, c67, c118, c28, c206, c21, c120, c24, c207, c136, c190, c40, c393, c184, c89] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c1183 := derived1183 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c393 := h 392 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, false), (⟨31, by decide⟩, false), (⟨49, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c190, some c315, some c143, some c352, some c73, some c165, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 57) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c190, c315, c143, c352, c73, c165] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c389, some c315, some c113, some c283, some c76, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 57) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c1057, c389, c315, c113, c283, c76] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c389 := h 388 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c113, some c65, some c310, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 57) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c1057, c113, c65, c310] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1193

end CochromaticTwenty.Certificates.B16_1_2
