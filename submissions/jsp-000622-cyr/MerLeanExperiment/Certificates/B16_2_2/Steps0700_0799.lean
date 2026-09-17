import MerLeanExperiment.Certificates.B16_2_2.Steps0600_0699

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1084 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1030, some c6, some c1058, some c1080, some c1003, some c100, some c1072, some c18, some c20, some c257, some c264, some c1081, some c1082, some c253, some c31, some c1083, some c344, some c219, some c57, some c349, some c159, some c225, some c128, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 57) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c1030, c6, c1058, c1080, c1003, c100, c1072, c18, c20, c257, c264, c1081, c1082, c253, c31, c1083, c344, c219, c57, c349, c159, c225, c128] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c1030 := derived1030 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c1058 := derived1058 a h
  have h3 : Entails.eval a c1080 := derived1080 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1072 := derived1072 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1081 := derived1081 a h
  have h12 : Entails.eval a c1082 := derived1082 a h
  have h13 : Entails.eval a c253 := h 252 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c1083 := derived1083 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c225 := h 224 (by decide)
  have h22 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c132, some c157, some c305, some c346, some c146, some c187, some c304, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c344, c132, c157, c305, c346, c146, c187, c304] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1085, some c134, some c305, some c132, some c145, some c948, some c307, some c187, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c1085, c134, c305, c132, c145, c948, c307, c187] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c1085 := derived1085 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c948 := derived948 a h
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1030, some c6, some c1058, some c20, some c1080, some c1003, some c18, some c100, some c380, some c1072, some c1084, some c1074, some c1086, some c192, some c14, some c957, some c965, some c742, some c1060, some c307, some c769, some c187, some c382, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1030, c6, c1058, c20, c1080, c1003, c18, c100, c380, c1072, c1084, c1074, c1086, c192, c14, c957, c965, c742, c1060, c307, c769, c187, c382] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1030 := derived1030 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c1058 := derived1058 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c1080 := derived1080 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c1072 := derived1072 a h
  have h10 : Entails.eval a c1084 := derived1084 a h
  have h11 : Entails.eval a c1074 := derived1074 a h
  have h12 : Entails.eval a c1086 := derived1086 a h
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c957 := derived957 a h
  have h16 : Entails.eval a c965 := derived965 a h
  have h17 : Entails.eval a c742 := derived742 a h
  have h18 : Entails.eval a c1060 := derived1060 a h
  have h19 : Entails.eval a c307 := h 306 (by decide)
  have h20 : Entails.eval a c769 := derived769 a h
  have h21 : Entails.eval a c187 := h 186 (by decide)
  have h22 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c193, some c192, some c18, some c14, some c111, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c1087, c193, c192, c18, c14, c111] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c132, some c52, some c305, some c146, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 57) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c344, c132, c52, c305, c146] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c921, some c117, some c23, some c165, some c171, some c360, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 57) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c921, c117, c23, c165, c171, c360] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c921 := derived921 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨18, by decide⟩, true), (⟨38, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c220, some c52, some c352, some c132, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 57) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c133, c220, c52, c352, c132] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c220 := h 219 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c18, some c111, some c14, some c6, some c1088, some c1003, some c1089, some c972, some c1090, some c1091, some c68, some c132, some c52, some c146, some c208, some c312, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 57) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c1087, c18, c111, c14, c6, c1088, c1003, c1089, c972, c1090, c1091, c68, c132, c52, c146, c208, c312] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1088 := derived1088 a h
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c1089 := derived1089 a h
  have h8 : Entails.eval a c972 := derived972 a h
  have h9 : Entails.eval a c1090 := derived1090 a h
  have h10 : Entails.eval a c1091 := derived1091 a h
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1088, some c1003, some c1087, some c6, some c18, some c111, some c14, some c1092, some c134, some c158, some c68, some c132, some c52, some c305, some c312, some c972, some c208, some c1090, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 57) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c1088, c1003, c1087, c6, c18, c111, c14, c1092, c134, c158, c68, c132, c52, c305, c312, c972, c208, c1090] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c1088 := derived1088 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c1092 := derived1092 a h
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c312 := h 311 (by decide)
  have h15 : Entails.eval a c972 := derived972 a h
  have h16 : Entails.eval a c208 := h 207 (by decide)
  have h17 : Entails.eval a c1090 := derived1090 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1094 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c167, some c165, some c86, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 57) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c167, c165, c86] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c167 := h 166 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨45, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨42, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c123, some c233, some c368, some c229, some c82, some c105, some c40, some c1018, some c242, some c179, some c356, some c380, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 57) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c23, c123, c233, c368, c229, c82, c105, c40, c1018, c242, c179, c356, c380] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c1018 := derived1018 a h
  have h9 : Entails.eval a c242 := h 241 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1096 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1093, some c1087, some c111, some c1094, some c1088, some c1003, some c1090, some c232, some c1095, some c171, some c754, some c360, some c363, some c380, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 57) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c1093, c1087, c111, c1094, c1088, c1003, c1090, c232, c1095, c171, c754, c360, c363, c380] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1094 := derived1094 a h
  have h4 : Entails.eval a c1088 := derived1088 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c1090 := derived1090 a h
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c1095 := derived1095 a h
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c754 := derived754 a h
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c971, some c7, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c1003, c971, c7] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c992, some c10, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c15, c992, c10] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c992 := derived992 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c718, some c198, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 57) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c1007, c718, c198] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c1087, some c1099, some c22, some c1005, some c167, some c26, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 57) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c194, c1087, c1099, c22, c1005, c167, c26] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c1099 := derived1099 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1005 := derived1005 a h
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1088, some c1097, some c111, some c1093, some c194, some c1096, some c3, some c15, some c1098, some c1019, some c105, some c1100, some c119, some c26, some c861, some c377, some c187, some c185, some c382, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 57) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c1087, c1088, c1097, c111, c1093, c194, c1096, c3, c15, c1098, c1019, c105, c1100, c119, c26, c861, c377, c187, c185, c382] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1093 := derived1093 a h
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c1096 := derived1096 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c1098 := derived1098 a h
  have h10 : Entails.eval a c1019 := derived1019 a h
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c1100 := derived1100 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c861 := derived861 a h
  have h16 : Entails.eval a c377 := h 376 (by decide)
  have h17 : Entails.eval a c187 := h 186 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c145, some c52, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 57) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c147, c145, c52] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1088, some c1097, some c111, some c194, some c119, some c34, some c260, some c117, some c224, some c1098, some c115, some c162, some c21, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 57) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1087, c1088, c1097, c111, c194, c119, c34, c260, c117, c224, c1098, c115, c162, c21] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c1098 := derived1098 a h
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1093, some c1101, some c78, some c167, some c1003, some c104, some c105, some c1087, some c52, some c133, some c68, some c70, some c1103, some c22, some c208, some c46, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 57) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c1093, c1101, c78, c167, c1003, c104, c105, c1087, c52, c133, c68, c70, c1103, c22, c208, c46] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c1101 := derived1101 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1087 := derived1087 a h
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c1103 := derived1103 a h
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, false), (⟨42, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c220, some c62, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 57) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c22, c220, c62] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c220 := h 219 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1093, some c194, some c1088, some c1003, some c1087, some c111, some c1097, some c1101, some c104, some c78, some c105, some c167, some c1104, some c132, some c68, some c133, some c54, some c1105, some c119, some c34, some c260, some c117, some c212, some c1098, some c115, some c162, some c21, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 57) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c1093, c194, c1088, c1003, c1087, c111, c1097, c1101, c104, c78, c105, c167, c1104, c132, c68, c133, c54, c1105, c119, c34, c260, c117, c212, c1098, c115, c162, c21] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c1088 := derived1088 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1097 := derived1097 a h
  have h7 : Entails.eval a c1101 := derived1101 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c167 := h 166 (by decide)
  have h12 : Entails.eval a c1104 := derived1104 a h
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c54 := h 53 (by decide)
  have h17 : Entails.eval a c1105 := derived1105 a h
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c117 := h 116 (by decide)
  have h22 : Entails.eval a c212 := h 211 (by decide)
  have h23 : Entails.eval a c1098 := derived1098 a h
  have h24 : Entails.eval a c115 := h 114 (by decide)
  have h25 : Entails.eval a c162 := h 161 (by decide)
  have h26 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1088, some c1093, some c194, some c1106, some c38, some c19, some c119, some c1099, some c32, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 57) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c1087, c1088, c1093, c194, c1106, c38, c19, c119, c1099, c32] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c1093 := derived1093 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c1106 := derived1106 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c1099 := derived1099 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c193, some c194, some c1107, some c1087, some c38, some c25, some c119, some c32, some c108, some c1099, some c39, some c8, some c15, some c258, some c255, some c1094, some c170, some c229, some c78, some c87, some c369, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 57) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c193, c194, c1107, c1087, c38, c25, c119, c32, c108, c1099, c39, c8, c15, c258, c255, c1094, c170, c229, c78, c87, c369] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c193 := h 192 (by decide)
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c1107 := derived1107 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c1099 := derived1099 a h
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c258 := h 257 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c1094 := derived1094 a h
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c78 := h 77 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1108, some c111, some c193, some c194, some c1107, some c15, some c1094, some c232, some c170, some c86, some c87, some c369, some c229, some c82, some c114, some c993, some c201, some c1105, some c52, some c132, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 57) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1087, c1108, c111, c193, c194, c1107, c15, c1094, c232, c170, c86, c87, c369, c229, c82, c114, c993, c201, c1105, c52, c132] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1108 := derived1108 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1107 := derived1107 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c1094 := derived1094 a h
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c993 := derived993 a h
  have h17 : Entails.eval a c201 := h 200 (by decide)
  have h18 : Entails.eval a c1105 := derived1105 a h
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1099, some c22, some c111, some c10, some c1016, some c993, some c320, some c220, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 57) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c1099, c22, c111, c10, c1016, c993, c320, c220] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c1099 := derived1099 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1016 := derived1016 a h
  have h5 : Entails.eval a c993 := derived993 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1111 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1108, some c111, some c193, some c194, some c1107, some c1109, some c1099, some c22, some c167, some c1094, some c78, some c86, some c3, some c754, some c1110, some c189, some c1100, some c114, some c105, some c92, some c7, some c375, some c589, some c383, some c185, some c366, some c253, some c370, some c231, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 57) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1087, c1108, c111, c193, c194, c1107, c1109, c1099, c22, c167, c1094, c78, c86, c3, c754, c1110, c189, c1100, c114, c105, c92, c7, c375, c589, c383, c185, c366, c253, c370, c231] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1108 := derived1108 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1107 := derived1107 a h
  have h6 : Entails.eval a c1109 := derived1109 a h
  have h7 : Entails.eval a c1099 := derived1099 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c1094 := derived1094 a h
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c754 := derived754 a h
  have h15 : Entails.eval a c1110 := derived1110 a h
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c1100 := derived1100 a h
  have h18 : Entails.eval a c114 := h 113 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c92 := h 91 (by decide)
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c375 := h 374 (by decide)
  have h23 : Entails.eval a c589 := derived589 a h
  have h24 : Entails.eval a c383 := h 382 (by decide)
  have h25 : Entails.eval a c185 := h 184 (by decide)
  have h26 : Entails.eval a c366 := h 365 (by decide)
  have h27 : Entails.eval a c253 := h 252 (by decide)
  have h28 : Entails.eval a c370 := h 369 (by decide)
  have h29 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1108, some c111, some c193, some c194, some c1107, some c1111, some c26, some c167, some c232, some c22, some c1099, some c15, some c196, some c170, some c87, some c369, some c82, some c105, some c7, some c40, some c583, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 57) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c1087, c1108, c111, c193, c194, c1107, c1111, c26, c167, c232, c22, c1099, c15, c196, c170, c87, c369, c82, c105, c7, c40, c583] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1108 := derived1108 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1107 := derived1107 a h
  have h6 : Entails.eval a c1111 := derived1111 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c1099 := derived1099 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c7 := h 6 (by decide)
  have h20 : Entails.eval a c40 := h 39 (by decide)
  have h21 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c201, some c52, some c54, some c144, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 57) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c970, c201, c52, c54, c144] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨51, by decide⟩, false), (⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c34, some c1113, some c40, some c7, some c251, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c111, c34, c1113, c40, c7, c251] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c1113 := derived1113 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1107, some c1087, some c193, some c1108, some c111, some c1112, some c119, some c34, some c117, some c3, some c1114, some c189, some c10, some c993, some c201, some c52, some c41, some c139, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1107, c1087, c193, c1108, c111, c1112, c119, c34, c117, c3, c1114, c189, c10, c993, c201, c52, c41, c139] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1107 := derived1107 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c1108 := derived1108 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1112 := derived1112 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1114 := derived1114 a h
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c993 := derived993 a h
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c52 := h 51 (by decide)
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1115, some c1107, some c1087, some c111, some c14, some c192, some c196, some c20, some c1113, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c1115, c1107, c1087, c111, c14, c192, c196, c20, c1113] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c1107 := derived1107 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c1113 := derived1113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨43, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨45, by decide⟩, false), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c156, some c151, some c46, some c59, some c82, some c1, some c717, some c242, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c132, c156, c151, c46, c59, c82, c1, c717, c242] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨43, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨45, by decide⟩, false), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1117, some c62, some c198, some c220, some c46, some c1053, some c139, some c43, some c82, some c1, some c316, some c242, some c217, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c1117, c62, c198, c220, c46, c1053, c139, c43, c82, c1, c316, c242, c217] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c1117 := derived1117 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c220 := h 219 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c1053 := derived1053 a h
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1116, some c25, some c1107, some c170, some c1115, some c20, some c38, some c6, some c1087, some c23, some c86, some c117, some c32, some c1118, some c161, some c82, some c107, some c39, some c87, some c258, some c373, some c229, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c1116, c25, c1107, c170, c1115, c20, c38, c6, c1087, c23, c86, c117, c32, c1118, c161, c82, c107, c39, c87, c258, c373, c229] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c1116 := derived1116 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c1107 := derived1107 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c1087 := derived1087 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c1118 := derived1118 a h
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c39 := h 38 (by decide)
  have h18 : Entails.eval a c87 := h 86 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c373 := h 372 (by decide)
  have h21 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1115, some c20, some c1116, some c25, some c38, some c6, some c1107, some c1087, some c170, some c1119, some c108, some c32, some c117, some c247, some c262, some c74, some c39, some c235, some c168, some c107, some c594, some c93, some c72, some c377, some c156, some c160, some c185, some c344, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c1115, c20, c1116, c25, c38, c6, c1107, c1087, c170, c1119, c108, c32, c117, c247, c262, c74, c39, c235, c168, c107, c594, c93, c72, c377, c156, c160, c185, c344] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c1115 := derived1115 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c1116 := derived1116 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c1107 := derived1107 a h
  have h7 : Entails.eval a c1087 := derived1087 a h
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c1119 := derived1119 a h
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c247 := h 246 (by decide)
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c594 := derived594 a h
  have h21 : Entails.eval a c93 := h 92 (by decide)
  have h22 : Entails.eval a c72 := h 71 (by decide)
  have h23 : Entails.eval a c377 := h 376 (by decide)
  have h24 : Entails.eval a c156 := h 155 (by decide)
  have h25 : Entails.eval a c160 := h 159 (by decide)
  have h26 : Entails.eval a c185 := h 184 (by decide)
  have h27 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1116, some c38, some c1115, some c6, some c1087, some c20, some c1120, some c14, some c108, some c32, some c261, some c247, some c262, some c471, some c74, some c39, some c107, some c93, some c377, some c376, some c184, some c382, some c183, some c658, some c168, some c371, some c237, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c1116, c38, c1115, c6, c1087, c20, c1120, c14, c108, c32, c261, c247, c262, c471, c74, c39, c107, c93, c377, c376, c184, c382, c183, c658, c168, c371, c237] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c1116 := derived1116 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c1120 := derived1120 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c262 := h 261 (by decide)
  have h13 : Entails.eval a c471 := derived471 a h
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c377 := h 376 (by decide)
  have h19 : Entails.eval a c376 := h 375 (by decide)
  have h20 : Entails.eval a c184 := h 183 (by decide)
  have h21 : Entails.eval a c382 := h 381 (by decide)
  have h22 : Entails.eval a c183 := h 182 (by decide)
  have h23 : Entails.eval a c658 := derived658 a h
  have h24 : Entails.eval a c168 := h 167 (by decide)
  have h25 : Entails.eval a c371 := h 370 (by decide)
  have h26 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨53, by decide⟩, false), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨47, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c237, some c363, some c168, some c382, some c183, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c237, c363, c168, c382, c183] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c237 := h 236 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨49, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c150, some c333, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c154, c150, c333] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨42, by decide⟩, false), (⟨53, by decide⟩, false), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c376, some c1122, some c374, some c658, some c1123, some c341, some c65, some c201, some c132, some c288, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c377, c376, c1122, c374, c658, c1123, c341, c65, c201, c132, c288] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c1122 := derived1122 a h
  have h3 : Entails.eval a c374 := h 373 (by decide)
  have h4 : Entails.eval a c658 := derived658 a h
  have h5 : Entails.eval a c1123 := derived1123 a h
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1116, some c25, some c38, some c1115, some c6, some c1107, some c1087, some c1121, some c189, some c196, some c174, some c14, some c108, some c32, some c261, some c247, some c262, some c471, some c74, some c1124, some c397, some c179, some c382, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1116, c25, c38, c1115, c6, c1107, c1087, c1121, c189, c196, c174, c14, c108, c32, c261, c247, c262, c471, c74, c1124, c397, c179, c382] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1116 := derived1116 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1107 := derived1107 a h
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c1121 := derived1121 a h
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c471 := derived471 a h
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c1124 := derived1124 a h
  have h20 : Entails.eval a c397 := derived397 a h
  have h21 : Entails.eval a c179 := h 178 (by decide)
  have h22 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1115, some c1125, some c192, some c14, some c108, some c1116, some c38, some c6, some c32, some c247, some c74, some c1107, some c25, some c172, some c118, some c262, some c237, some c373, some c39, some c471, some c92, some c107, some c93, some c377, some c376, some c1122, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c1087, c1115, c1125, c192, c14, c108, c1116, c38, c6, c32, c247, c74, c1107, c25, c172, c118, c262, c237, c373, c39, c471, c92, c107, c93, c377, c376, c1122] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1115 := derived1115 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1116 := derived1116 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c1107 := derived1107 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c237 := h 236 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c471 := derived471 a h
  have h21 : Entails.eval a c92 := h 91 (by decide)
  have h22 : Entails.eval a c107 := h 106 (by decide)
  have h23 : Entails.eval a c93 := h 92 (by decide)
  have h24 : Entails.eval a c377 := h 376 (by decide)
  have h25 : Entails.eval a c376 := h 375 (by decide)
  have h26 : Entails.eval a c1122 := derived1122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1107, some c1115, some c6, some c1116, some c38, some c25, some c1125, some c192, some c172, some c14, some c108, some c32, some c118, some c247, some c262, some c39, some c1126, some c174, some c368, some c20, some c231, some c107, some c242, some c93, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c1087, c1107, c1115, c6, c1116, c38, c25, c1125, c192, c172, c14, c108, c32, c118, c247, c262, c39, c1126, c174, c368, c20, c231, c107, c242, c93] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1107 := derived1107 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1116 := derived1116 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c1125 := derived1125 a h
  have h8 : Entails.eval a c192 := h 191 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c262 := h 261 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c1126 := derived1126 a h
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c20 := h 19 (by decide)
  have h21 : Entails.eval a c231 := h 230 (by decide)
  have h22 : Entails.eval a c107 := h 106 (by decide)
  have h23 : Entails.eval a c242 := h 241 (by decide)
  have h24 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c358, some c237, some c382, some c373, some c471, some c86, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c357, c358, c237, c382, c373, c471, c86] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c471 := derived471 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c368, some c357, some c1128, some c172, some c372, some c86, some c471, some c383, some c382, some c184, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c375, c368, c357, c1128, c172, c372, c86, c471, c383, c382, c184] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c1128 := derived1128 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c471 := derived471 a h
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c1129, some c1127, some c374, some c172, some c372, some c86, some c92, some c471, some c107, some c28, some c168, some c8, some c667, some c589, some c257, some c264, some c184, some c230, some c382, some c161, some c178, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c1087, c1129, c1127, c374, c172, c372, c86, c92, c471, c107, c28, c168, c8, c667, c589, c257, c264, c184, c230, c382, c161, c178] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c374 := h 373 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c471 := derived471 a h
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c667 := derived667 a h
  have h14 : Entails.eval a c589 := derived589 a h
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c264 := h 263 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c230 := h 229 (by decide)
  have h19 : Entails.eval a c382 := h 381 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c74, some c1127, some c1087, some c1129, some c1130, some c237, some c236, some c373, some c257, some c92, some c231, some c513, some c161, some c254, some c178, some c363, some c382, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c93, c74, c1127, c1087, c1129, c1130, c237, c236, c373, c257, c92, c231, c513, c161, c254, c178, c363, c382] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c1129 := derived1129 a h
  have h5 : Entails.eval a c1130 := derived1130 a h
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  have h12 : Entails.eval a c513 := derived513 a h
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨42, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c237, some c236, some c373, some c257, some c264, some c90, some c92, some c503, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c237, c236, c373, c257, c264, c90, c92, c503] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c237 := h 236 (by decide)
  have h1 : Entails.eval a c236 := h 235 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c503 := derived503 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨45, by decide⟩, true), (⟨42, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c372, some c86, some c90, some c111, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c371, c372, c86, c90, c111] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c74, some c1127, some c1087, some c1131, some c1133, some c237, some c1132, some c373, some c370, some c90, some c231, some c111, some c105, some c257, some c14, some c1006, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c93, c74, c1127, c1087, c1131, c1133, c237, c1132, c373, c370, c90, c231, c111, c105, c257, c14, c1006] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c1131 := derived1131 a h
  have h5 : Entails.eval a c1133 := derived1133 a h
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c1132 := derived1132 a h
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c257 := h 256 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c1006 := derived1006 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c90, some c253, some c111, some c184, some c179, some c14, some c589, some c190, some c185, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c26, c90, c253, c111, c184, c179, c14, c589, c190, c185] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c589 := derived589 a h
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨24, by decide⟩, true), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c167, some c373, some c20, some c28, some c107, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c167, c373, c20, c28, c107] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c167 := h 166 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c74, some c1127, some c1087, some c1134, some c124, some c263, some c1136, some c26, some c1135, some c253, some c179, some c113, some c161, some c358, some c230, some c374, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c93, c74, c1127, c1087, c1134, c124, c263, c1136, c26, c1135, c253, c179, c113, c161, c358, c230, c374] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c1134 := derived1134 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c1136 := derived1136 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1135 := derived1135 a h
  have h10 : Entails.eval a c253 := h 252 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c230 := h 229 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨45, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c258, some c179, some c161, some c358, some c230, some c374, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c253, c258, c179, c161, c358, c230, c374] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c161 := h 160 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c26, some c34, some c372, some c373, some c471, some c252, some c184, some c364, some c589, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c263, c26, c34, c372, c373, c471, c252, c184, c364, c589] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c471 := derived471 a h
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c589 := derived589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1087, some c124, some c263, some c1139, some c253, some c255, some c1138, some c185, some c1133, some c168, some c364, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1127, c1087, c124, c263, c1139, c253, c255, c1138, c185, c1133, c168, c364] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c1139 := derived1139 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c1138 := derived1138 a h
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c1133 := derived1133 a h
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨44, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c589, some c185, some c364, some c168, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c184, c589, c185, c364, c168] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, true), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c26, some c90, some c258, some c105, some c231, some c92, some c370, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c373, c26, c90, c258, c105, c231, c92, c370] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨45, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c107, some c91, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c105, c107, c91] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c1127, some c1087, some c1133, some c1142, some c1143, some c20, some c1006, some c97, some c589, some c254, some c366, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c74, c1127, c1087, c1133, c1142, c1143, c20, c1006, c97, c589, c254, c366] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c1127 := derived1127 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1133 := derived1133 a h
  have h4 : Entails.eval a c1142 := derived1142 a h
  have h5 : Entails.eval a c1143 := derived1143 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1006 := derived1006 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c589 := derived589 a h
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c20, some c1006, some c167, some c257, some c92, some c231, some c368, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1127, c20, c1006, c167, c257, c92, c231, c368] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c1006 := derived1006 a h
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c231 := h 230 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c264, some c231, some c1052, some c161, some c51, some c632, some c135, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c257, c264, c231, c1052, c161, c51, c632, c135] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c1052 := derived1052 a h
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c632 := derived632 a h
  have h7 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, false), (⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1146, some c236, some c634, some c368, some c113, some c231, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c1146, c236, c634, c368, c113, c231] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c1146 := derived1146 a h
  have h1 : Entails.eval a c236 := h 235 (by decide)
  have h2 : Entails.eval a c634 := derived634 a h
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1145, some c107, some c1147, some c14, some c15, some c194, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1127, c1145, c107, c1147, c14, c15, c194] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1145 := derived1145 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c74, some c1087, some c1137, some c1140, some c1144, some c1148, some c374, some c172, some c372, some c26, some c86, some c255, some c471, some c658, some c383, some c382, some c184, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c93, c74, c1087, c1137, c1140, c1144, c1148, c374, c172, c372, c26, c86, c255, c471, c658, c383, c382, c184] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c1137 := derived1137 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c1144 := derived1144 a h
  have h6 : Entails.eval a c1148 := derived1148 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c471 := derived471 a h
  have h14 : Entails.eval a c658 := derived658 a h
  have h15 : Entails.eval a c383 := h 382 (by decide)
  have h16 : Entails.eval a c382 := h 381 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c93, some c1149, some c1003, some c1088, some c1097, some c7, some c18, some c107, some c194, some c19, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1087, c93, c1149, c1003, c1088, c1097, c7, c18, c107, c194, c19] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c1149 := derived1149 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1088 := derived1088 a h
  have h5 : Entails.eval a c1097 := derived1097 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c1088, some c184, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1003, c1088, c184] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1151, some c1127, some c7, some c184, some c105, some c107, some c193, some c192, some c124, some c80, some c8, some c14, some c168, some c84, some c172, some c1147, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1151, c1127, c7, c184, c105, c107, c193, c192, c124, c80, c8, c14, c168, c84, c172, c1147] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1151 := derived1151 a h
  have h1 : Entails.eval a c1127 := derived1127 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c1147 := derived1147 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c604, some c622, some c614, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c105, c604, c622, c614] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c604 := derived604 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c614 := derived614 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, true), (⟨55, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1087, some c264, some c254, some c34, some c102, some c111, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c1127, c1087, c264, c254, c34, c102, c111] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c78, some c167, some c193, some c194, some c1127, some c185, some c378, some c861, some c179, some c113, some c162, some c229, some c119, some c248, some c1153, some c1154, some c40, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c6, c78, c167, c193, c194, c1127, c185, c378, c861, c179, c113, c162, c229, c119, c248, c1153, c1154, c40] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c861 := derived861 a h
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c1153 := derived1153 a h
  have h16 : Entails.eval a c1154 := derived1154 a h
  have h17 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c222, some c67, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c228, c222, c67] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨38, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨42, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨46, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c369, some c330, some c81, some c594, some c107, some c248, some c8, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 57) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c108, c369, c330, c81, c594, c107, c248, c8] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c594 := derived594 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c375, some c236, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 57) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c374, c375, c236] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c119, some c78, some c167, some c193, some c194, some c1087, some c379, some c1008, some c246, some c111, some c108, some c667, some c84, some c117, some c1156, some c1157, some c1158, some c362, some c235, some c248, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 57) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c6, c119, c78, c167, c193, c194, c1087, c379, c1008, c246, c111, c108, c667, c84, c117, c1156, c1157, c1158, c362, c235, c248] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1008 := derived1008 a h
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c667 := derived667 a h
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c1156 := derived1156 a h
  have h16 : Entails.eval a c1157 := derived1157 a h
  have h17 : Entails.eval a c1158 := derived1158 a h
  have h18 : Entails.eval a c362 := h 361 (by decide)
  have h19 : Entails.eval a c235 := h 234 (by decide)
  have h20 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c78, some c167, some c193, some c194, some c1159, some c185, some c248, some c28, some c107, some c81, some c861, some c378, some c1127, some c102, some c84, some c368, some c363, some c374, some c235, some c263, some c250, some c117, some c663, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 57) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c6, c78, c167, c193, c194, c1159, c185, c248, c28, c107, c81, c861, c378, c1127, c102, c84, c368, c363, c374, c235, c263, c250, c117, c663] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1159 := derived1159 a h
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c861 := derived861 a h
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c1127 := derived1127 a h
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c374 := h 373 (by decide)
  have h19 : Entails.eval a c235 := h 234 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c250 := h 249 (by decide)
  have h22 : Entails.eval a c117 := h 116 (by decide)
  have h23 : Entails.eval a c663 := derived663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c193, some c194, some c1159, some c185, some c248, some c28, some c107, some c119, some c78, some c167, some c1087, some c81, some c162, some c1160, some c111, some c10, some c34, some c117, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 57) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c6, c193, c194, c1159, c185, c248, c28, c107, c119, c78, c167, c1087, c81, c162, c1160, c111, c10, c34, c117] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c1159 := derived1159 a h
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c1087 := derived1087 a h
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c1160 := derived1160 a h
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨22, by decide⟩, true), (⟨18, by decide⟩, false), (⟨54, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c34, some c245, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 57) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c98, c34, c245] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c119, some c78, some c167, some c193, some c194, some c1087, some c1159, some c1162, some c111, some c108, some c1161, some c369, some c81, some c107, some c19, some c1155, some c184, some c196, some c189, some c634, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 57) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c6, c119, c78, c167, c193, c194, c1087, c1159, c1162, c111, c108, c1161, c369, c81, c107, c19, c1155, c184, c196, c189, c634] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c1159 := derived1159 a h
  have h8 : Entails.eval a c1162 := derived1162 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c1161 := derived1161 a h
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c1155 := derived1155 a h
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c196 := h 195 (by decide)
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c634 := derived634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c78, some c167, some c1127, some c1087, some c119, some c1163, some c74, some c108, some c98, some c34, some c263, some c250, some c117, some c102, some c359, some c105, some c1158, some c10, some c1010, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 57) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c6, c78, c167, c1127, c1087, c119, c1163, c74, c108, c98, c34, c263, c250, c117, c102, c359, c105, c1158, c10, c1010] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c1087 := derived1087 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c1163 := derived1163 a h
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c1158 := derived1158 a h
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c1010 := derived1010 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨42, by decide⟩, true), (⟨54, by decide⟩, true), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c34, some c264, some c263, some c250, some c40, some c233, some c102, some c359, some c105, some c1158, some c368, some c82, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 57) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c98, c34, c264, c263, c250, c40, c233, c102, c359, c105, c1158, c368, c82] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c1158 := derived1158 a h
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨1, by decide⟩, true), (⟨47, by decide⟩, false), (⟨23, by decide⟩, true), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c250, some c359, some c1158, some c368, some c82, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 57) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c263, c250, c359, c1158, c368, c82] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c1158 := derived1158 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨47, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1166, some c35, some c30, some c258, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 57) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c1166, c35, c30, c258] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨47, by decide⟩, false), (⟨56, by decide⟩, false), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c383, some c356, some c359, some c368, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 57) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c378, c383, c356, c359, c368] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨54, by decide⟩, true), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1165, some c15, some c8, some c98, some c233, some c1167, some c1168, some c104, some c105, some c102, some c19, some c382, some c196, some c184, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 57) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c1165, c15, c8, c98, c233, c1167, c1168, c104, c105, c102, c19, c382, c196, c184] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c1165 := derived1165 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c1167 := derived1167 a h
  have h6 : Entails.eval a c1168 := derived1168 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c382 := h 381 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1087, some c108, some c1127, some c6, some c78, some c194, some c193, some c167, some c1099, some c8, some c1169, some c257, some c264, some c229, some c35, some c30, some c369, some c256, some c104, some c360, some c1143, some c368, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 57) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c1087, c108, c1127, c6, c78, c194, c193, c167, c1099, c8, c1169, c257, c264, c229, c35, c30, c369, c256, c104, c360, c1143, c368] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c1087 := derived1087 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c1099 := derived1099 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c1169 := derived1169 a h
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c104 := h 103 (by decide)
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c1143 := derived1143 a h
  have h21 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c107, some c35, some c255, some c103, some c80, some c1049, some c370, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 57) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c105, c107, c35, c255, c103, c80, c1049, c370] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨42, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c257, some c229, some c22, some c264, some c23, some c1087, some c368, some c359, some c254, some c7, some c171, some c126, some c14, some c1088, some c194, some c1099, some c15, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 57) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1127, c257, c229, c22, c264, c23, c1087, c368, c359, c254, c7, c171, c126, c14, c1088, c194, c1099, c15] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c1087 := derived1087 a h
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c1088 := derived1088 a h
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c1099 := derived1099 a h
  have h17 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c257, some c264, some c30, some c34, some c1087, some c22, some c229, some c1171, some c1172, some c92, some c360, some c369, some c1003, some c589, some c126, some c80, some c20, some c194, some c193, some c1099, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 57) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c1127, c257, c264, c30, c34, c1087, c22, c229, c1171, c1172, c92, c360, c369, c1003, c589, c126, c80, c20, c194, c193, c1099] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c1087 := derived1087 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c1171 := derived1171 a h
  have h9 : Entails.eval a c1172 := derived1172 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c1003 := derived1003 a h
  have h14 : Entails.eval a c589 := derived589 a h
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c20 := h 19 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c1099 := derived1099 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1087, some c257, some c264, some c34, some c23, some c30, some c1173, some c165, some c371, some c14, some c3, some c194, some c193, some c167, some c15, some c107, some c1099, some c97, some c92, some c589, some c383, some c375, some c185, some c366, some c253, some c370, some c231, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 57) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c1127, c1087, c257, c264, c34, c23, c30, c1173, c165, c371, c14, c3, c194, c193, c167, c15, c107, c1099, c97, c92, c589, c383, c375, c185, c366, c253, c370, c231] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1087 := derived1087 a h
  have h2 : Entails.eval a c257 := h 256 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1173 := derived1173 a h
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c1099 := derived1099 a h
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c92 := h 91 (by decide)
  have h20 : Entails.eval a c589 := derived589 a h
  have h21 : Entails.eval a c383 := h 382 (by decide)
  have h22 : Entails.eval a c375 := h 374 (by decide)
  have h23 : Entails.eval a c185 := h 184 (by decide)
  have h24 : Entails.eval a c366 := h 365 (by decide)
  have h25 : Entails.eval a c253 := h 252 (by decide)
  have h26 : Entails.eval a c370 := h 369 (by decide)
  have h27 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c193, some c1099, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 57) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c194, c193, c1099] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c1099 := derived1099 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1174, some c33, some c27, some c40, some c1127, some c1087, some c1175, some c20, some c14, some c1014, some c192, some c165, some c1099, some c23, some c86, some c176, some c263, some c250, some c372, some c237, some c255, some c258, some c942, some c231, some c368, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 57) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c1174, c33, c27, c40, c1127, c1087, c1175, c20, c14, c1014, c192, c165, c1099, c23, c86, c176, c263, c250, c372, c237, c255, c258, c942, c231, c368] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c1174 := derived1174 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1087 := derived1087 a h
  have h6 : Entails.eval a c1175 := derived1175 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c1014 := derived1014 a h
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c1099 := derived1099 a h
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c250 := h 249 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c255 := h 254 (by decide)
  have h21 : Entails.eval a c258 := h 257 (by decide)
  have h22 : Entails.eval a c942 := derived942 a h
  have h23 : Entails.eval a c231 := h 230 (by decide)
  have h24 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c6, some c20, some c14, some c192, some c196, some c1003, some c18, some c79, some c1014, some c171, some c87, some c23, some c86, some c176, some c250, some c373, some c1086, some c8, some c1015, some c889, some c179, some c377, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 57) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c1127, c6, c20, c14, c192, c196, c1003, c18, c79, c1014, c171, c87, c23, c86, c176, c250, c373, c1086, c8, c1015, c889, c179, c377] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c1014 := derived1014 a h
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c373 := h 372 (by decide)
  have h17 : Entails.eval a c1086 := derived1086 a h
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c1015 := derived1015 a h
  have h20 : Entails.eval a c889 := derived889 a h
  have h21 : Entails.eval a c179 := h 178 (by decide)
  have h22 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1008, some c381, some c104, some c1003, some c1155, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 57) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c1008, c381, c104, c1003, c1155] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c1008 := derived1008 a h
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1155 := derived1155 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1177, some c194, some c15, some c8, some c1094, some c22, some c1178, some c1170, some c377, some c589, some c356, some c7, some c79, some c370, some c171, some c87, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 57) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1177, c194, c15, c8, c1094, c22, c1178, c1170, c377, c589, c356, c7, c79, c370, c171, c87] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c1094 := derived1094 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1178 := derived1178 a h
  have h7 : Entails.eval a c1170 := derived1170 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c589 := derived589 a h
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c40, some c264, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 57) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c34, c40, c264] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1175, some c119, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 57) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1175, c119] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1175 := derived1175 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1182 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c14, some c196, some c1003, some c79, some c1014, some c1127, some c171, some c23, some c250, some c6, some c1090, some c1177, some c1180, some c1176, some c359, some c368, some c229, some c356, some c242, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 57) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c20, c14, c196, c1003, c79, c1014, c1127, c171, c23, c250, c6, c1090, c1177, c1180, c1176, c359, c368, c229, c356, c242] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1014 := derived1014 a h
  have h6 : Entails.eval a c1127 := derived1127 a h
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c1090 := derived1090 a h
  have h12 : Entails.eval a c1177 := derived1177 a h
  have h13 : Entails.eval a c1180 := derived1180 a h
  have h14 : Entails.eval a c1176 := derived1176 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1127, some c1180, some c1087, some c6, some c20, some c14, some c1177, some c192, some c196, some c1003, some c79, some c1090, some c1014, some c171, some c23, some c86, some c264, some c250, some c33, some c1099, some c176, some c191, some c1182, some c1008, some c381, some c179, some c366, some c364, some c242, some c368, some c372, some c229, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 57) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1127, c1180, c1087, c6, c20, c14, c1177, c192, c196, c1003, c79, c1090, c1014, c171, c23, c86, c264, c250, c33, c1099, c176, c191, c1182, c1008, c381, c179, c366, c364, c242, c368, c372, c229] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c1180 := derived1180 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c1177 := derived1177 a h
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c1003 := derived1003 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c1090 := derived1090 a h
  have h12 : Entails.eval a c1014 := derived1014 a h
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c264 := h 263 (by decide)
  have h17 : Entails.eval a c250 := h 249 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c1099 := derived1099 a h
  have h20 : Entails.eval a c176 := h 175 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c1182 := derived1182 a h
  have h23 : Entails.eval a c1008 := derived1008 a h
  have h24 : Entails.eval a c381 := h 380 (by decide)
  have h25 : Entails.eval a c179 := h 178 (by decide)
  have h26 : Entails.eval a c366 := h 365 (by decide)
  have h27 : Entails.eval a c364 := h 363 (by decide)
  have h28 : Entails.eval a c242 := h 241 (by decide)
  have h29 : Entails.eval a c368 := h 367 (by decide)
  have h30 : Entails.eval a c372 := h 371 (by decide)
  have h31 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1183

end CochromaticTwenty.Certificates.B16_2_2
