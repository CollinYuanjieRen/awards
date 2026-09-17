import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Steps0200_0299

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1203 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1189, some c1125, some c746, some c824, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 31) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c1189, c1125, c746, c824] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c1189 := derived1189 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c746 := h 745 (by decide)
  have h3 : Entails.eval a c824 := h 823 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1189, some c1125, some c1203, some c780, some c34, some c12, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 31) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c1193, c1189, c1125, c1203, c780, c34, c12] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1203 := derived1203 a h
  have h4 : Entails.eval a c780 := h 779 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c149, some c260, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 31) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c149, c260] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c149 := h 148 (by decide)
  have h1 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1206 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c1205, some c1149, some c577, some c678, some c492, some c726, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 31) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c66, c1205, c1149, c577, c678, c492, c726] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1149 := derived1149 a h
  have h3 : Entails.eval a c577 := h 576 (by decide)
  have h4 : Entails.eval a c678 := h 677 (by decide)
  have h5 : Entails.eval a c492 := h 491 (by decide)
  have h6 : Entails.eval a c726 := h 725 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1201, some c1193, some c1189, some c1125, some c66, some c1202, some c1204, some c1206, some c780, some c406, some c266, some c623, some c65, some c536, some c90, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 31) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c1201, c1193, c1189, c1125, c66, c1202, c1204, c1206, c780, c406, c266, c623, c65, c536, c90] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c1201 := derived1201 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1202 := derived1202 a h
  have h6 : Entails.eval a c1204 := derived1204 a h
  have h7 : Entails.eval a c1206 := derived1206 a h
  have h8 : Entails.eval a c780 := h 779 (by decide)
  have h9 : Entails.eval a c406 := h 405 (by decide)
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c623 := h 622 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c536 := h 535 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1201, some c1193, some c1189, some c1125, some c59, some c90, some c61, some c116, some c807, some c568, some c1203, some c34, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 31) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c1201, c1193, c1189, c1125, c59, c90, c61, c116, c807, c568, c1203, c34] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c1201 := derived1201 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c807 := h 806 (by decide)
  have h9 : Entails.eval a c568 := h 567 (by decide)
  have h10 : Entails.eval a c1203 := derived1203 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1209 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1201, some c1208, some c1204, some c1202, some c1193, some c1189, some c1125, some c420, some c464, some c726, some c503, some c678, some c649, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 31) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c1201, c1208, c1204, c1202, c1193, c1189, c1125, c420, c464, c726, c503, c678, c649] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c1201 := derived1201 a h
  have h1 : Entails.eval a c1208 := derived1208 a h
  have h2 : Entails.eval a c1204 := derived1204 a h
  have h3 : Entails.eval a c1202 := derived1202 a h
  have h4 : Entails.eval a c1193 := derived1193 a h
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c1125 := derived1125 a h
  have h7 : Entails.eval a c420 := h 419 (by decide)
  have h8 : Entails.eval a c464 := h 463 (by decide)
  have h9 : Entails.eval a c726 := h 725 (by decide)
  have h10 : Entails.eval a c503 := h 502 (by decide)
  have h11 : Entails.eval a c678 := h 677 (by decide)
  have h12 : Entails.eval a c649 := h 648 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1201, some c1125, some c1208, some c66, some c1204, some c1207, some c1209, some c43, some c141, some c19, some c173, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 31) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c1201, c1125, c1208, c66, c1204, c1207, c1209, c43, c141, c19, c173] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c1201 := derived1201 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1208 := derived1208 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1204 := derived1204 a h
  have h5 : Entails.eval a c1207 := derived1207 a h
  have h6 : Entails.eval a c1209 := derived1209 a h
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1193, some c1189, some c1125, some c1201, some c1210, some c71, some c304, some c64, some c211, some c112, some c204, some c61, some c24, some c591, some c608, some c796, some c66, some c633, some c614, some c764, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 31) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c1193, c1189, c1125, c1201, c1210, c71, c304, c64, c211, c112, c204, c61, c24, c591, c608, c796, c66, c633, c614, c764] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c1193 := derived1193 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1201 := derived1201 a h
  have h4 : Entails.eval a c1210 := derived1210 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c591 := h 590 (by decide)
  have h14 : Entails.eval a c608 := h 607 (by decide)
  have h15 : Entails.eval a c796 := h 795 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c633 := h 632 (by decide)
  have h18 : Entails.eval a c614 := h 613 (by decide)
  have h19 : Entails.eval a c764 := h 763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1212 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1211, some c1193, some c1189, some c1125, some c15, some c780, some c665, some c266, some c474, some c664, some c141, some c763, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 31) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c1211, c1193, c1189, c1125, c15, c780, c665, c266, c474, c664, c141, c763] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c780 := h 779 (by decide)
  have h6 : Entails.eval a c665 := h 664 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c474 := h 473 (by decide)
  have h9 : Entails.eval a c664 := h 663 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c763 := h 762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1212, some c1211, some c1193, some c1125, some c276, some c141, some c210, some c836, some c579, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 31) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c1212, c1211, c1193, c1125, c276, c141, c210, c836, c579] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c1212 := derived1212 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1193 := derived1193 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c836 := h 835 (by decide)
  have h8 : Entails.eval a c579 := h 578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1214 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1211, some c1193, some c1189, some c1125, some c1212, some c1213, some c61, some c71, some c14, some c65, some c59, some c24, some c617, some c284, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 31) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c1211, c1193, c1189, c1125, c1212, c1213, c61, c71, c14, c65, c59, c24, c617, c284] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1212 := derived1212 a h
  have h5 : Entails.eval a c1213 := derived1213 a h
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c617 := h 616 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1215 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1214, some c1211, some c1193, some c1189, some c1125, some c61, some c71, some c14, some c601, some c24, some c88, some c818, some c843, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 31) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c1214, c1211, c1193, c1189, c1125, c61, c71, c14, c601, c24, c88, c818, c843] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c1214 := derived1214 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1193 := derived1193 a h
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c601 := h 600 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c818 := h 817 (by decide)
  have h12 : Entails.eval a c843 := h 842 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1216 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1214, some c1211, some c1189, some c1215, some c276, some c811, some c263, some c256, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 31) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c1214, c1211, c1189, c1215, c276, c811, c263, c256] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c1214 := derived1214 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1215 := derived1215 a h
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c811 := h 810 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1217 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1189, some c276, some c22, some c256, some c145, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1217 : lratChecker f1217 p1217 = .success := by decide +kernel
theorem unsat1217 : Unsatisfiable (PosFin 31) f1217 := by
  apply lratCheckerSound f1217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1217
  · intro a ha; simp [p1217] at ha; subst a; trivial
  · exact checked1217
theorem derived1217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1217 := by
  apply localUnsat_implies_entails f1217 [c1189, c276, c22, c256, c145] c1217 unsat1217 (by rfl) a
  have h0 : Entails.eval a c1189 := derived1189 a h
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1218 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1211, some c1193, some c1125, some c304, some c328, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1218 : lratChecker f1218 p1218 = .success := by decide +kernel
theorem unsat1218 : Unsatisfiable (PosFin 31) f1218 := by
  apply lratCheckerSound f1218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1218
  · intro a ha; simp [p1218] at ha; subst a; trivial
  · exact checked1218
theorem derived1218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1218 := by
  apply localUnsat_implies_entails f1218 [c1211, c1193, c1125, c304, c328] c1218 unsat1218 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c304 := h 303 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1219 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1218, some c1211, some c1193, some c1189, some c1125, some c24, some c15, some c1216, some c61, some c31, some c1113, some c71, some c420, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1219 : lratChecker f1219 p1219 = .success := by decide +kernel
theorem unsat1219 : Unsatisfiable (PosFin 31) f1219 := by
  apply lratCheckerSound f1219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1219
  · intro a ha; simp [p1219] at ha; subst a; trivial
  · exact checked1219
theorem derived1219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1219 := by
  apply localUnsat_implies_entails f1219 [c1218, c1211, c1193, c1189, c1125, c24, c15, c1216, c61, c31, c1113, c71, c420] c1219 unsat1219 (by rfl) a
  have h0 : Entails.eval a c1218 := derived1218 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c1193 := derived1193 a h
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c1216 := derived1216 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c1113 := derived1113 a h
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c420 := h 419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1220 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1219, some c1218, some c1211, some c1193, some c1189, some c1125, some c15, some c1216, some c31, some c1113, some c274, some c445, some c528, some c422, some c50, some c64, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1220 : lratChecker f1220 p1220 = .success := by decide +kernel
theorem unsat1220 : Unsatisfiable (PosFin 31) f1220 := by
  apply lratCheckerSound f1220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1220
  · intro a ha; simp [p1220] at ha; subst a; trivial
  · exact checked1220
theorem derived1220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1220 := by
  apply localUnsat_implies_entails f1220 [c1219, c1218, c1211, c1193, c1189, c1125, c15, c1216, c31, c1113, c274, c445, c528, c422, c50, c64] c1220 unsat1220 (by rfl) a
  have h0 : Entails.eval a c1219 := derived1219 a h
  have h1 : Entails.eval a c1218 := derived1218 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1193 := derived1193 a h
  have h4 : Entails.eval a c1189 := derived1189 a h
  have h5 : Entails.eval a c1125 := derived1125 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c1216 := derived1216 a h
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c1113 := derived1113 a h
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c445 := h 444 (by decide)
  have h12 : Entails.eval a c528 := h 527 (by decide)
  have h13 : Entails.eval a c422 := h 421 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1221 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1189, some c1125, some c1211, some c1219, some c276, some c1220, some c1217, some c22, some c90, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1221 : lratChecker f1221 p1221 = .success := by decide +kernel
theorem unsat1221 : Unsatisfiable (PosFin 31) f1221 := by
  apply lratCheckerSound f1221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1221
  · intro a ha; simp [p1221] at ha; subst a; trivial
  · exact checked1221
theorem derived1221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1221 := by
  apply localUnsat_implies_entails f1221 [c1189, c1125, c1211, c1219, c276, c1220, c1217, c22, c90] c1221 unsat1221 (by rfl) a
  have h0 : Entails.eval a c1189 := derived1189 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1219 := derived1219 a h
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c1220 := derived1220 a h
  have h6 : Entails.eval a c1217 := derived1217 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1222 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c1189, some c1125, some c1217, some c22, some c90, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1222 : lratChecker f1222 p1222 = .success := by decide +kernel
theorem unsat1222 : Unsatisfiable (PosFin 31) f1222 := by
  apply lratCheckerSound f1222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1222
  · intro a ha; simp [p1222] at ha; subst a; trivial
  · exact checked1222
theorem derived1222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1222 := by
  apply localUnsat_implies_entails f1222 [c276, c1189, c1125, c1217, c22, c90] c1222 unsat1222 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1217 := derived1217 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1223 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1221, some c1125, some c1187, some c553, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1223 : lratChecker f1223 p1223 = .success := by decide +kernel
theorem unsat1223 : Unsatisfiable (PosFin 31) f1223 := by
  apply lratCheckerSound f1223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1223
  · intro a ha; simp [p1223] at ha; subst a; trivial
  · exact checked1223
theorem derived1223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1223 := by
  apply localUnsat_implies_entails f1223 [c1221, c1125, c1187, c553] c1223 unsat1223 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c1187 := derived1187 a h
  have h3 : Entails.eval a c553 := h 552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1224 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c276, some c263, some c256, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1224 : lratChecker f1224 p1224 = .success := by decide +kernel
theorem unsat1224 : Unsatisfiable (PosFin 31) f1224 := by
  apply lratCheckerSound f1224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1224
  · intro a ha; simp [p1224] at ha; subst a; trivial
  · exact checked1224
theorem derived1224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1224 := by
  apply localUnsat_implies_entails f1224 [c276, c263, c256] c1224 unsat1224 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1225 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c308, some c1189, some c1222, some c15, some c1223, some c1224, some c145, some c59, some c304, some c112, some c211, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1225 : lratChecker f1225 p1225 = .success := by decide +kernel
theorem unsat1225 : Unsatisfiable (PosFin 31) f1225 := by
  apply lratCheckerSound f1225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1225
  · intro a ha; simp [p1225] at ha; subst a; trivial
  · exact checked1225
theorem derived1225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1225 := by
  apply localUnsat_implies_entails f1225 [c1125, c308, c1189, c1222, c15, c1223, c1224, c145, c59, c304, c112, c211] c1225 unsat1225 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1222 := derived1222 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1226 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1189, some c1125, some c61, some c59, some c71, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1226 : lratChecker f1226 p1226 = .success := by decide +kernel
theorem unsat1226 : Unsatisfiable (PosFin 31) f1226 := by
  apply lratCheckerSound f1226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1226
  · intro a ha; simp [p1226] at ha; subst a; trivial
  · exact checked1226
theorem derived1226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1226 := by
  apply localUnsat_implies_entails f1226 [c1189, c1125, c61, c59, c71] c1226 unsat1226 (by rfl) a
  have h0 : Entails.eval a c1189 := derived1189 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1227 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c308, some c304, some c328, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1227 : lratChecker f1227 p1227 = .success := by decide +kernel
theorem unsat1227 : Unsatisfiable (PosFin 31) f1227 := by
  apply lratCheckerSound f1227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1227
  · intro a ha; simp [p1227] at ha; subst a; trivial
  · exact checked1227
theorem derived1227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1227 := by
  apply localUnsat_implies_entails f1227 [c1125, c308, c304, c328] c1227 unsat1227 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1228 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1221, some c1189, some c1125, some c308, some c1225, some c1227, some c23, some c24, some c15, some c283, some c61, some c1226, some c355, some c116, some c36, some c210, some c342, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1228 : lratChecker f1228 p1228 = .success := by decide +kernel
theorem unsat1228 : Unsatisfiable (PosFin 31) f1228 := by
  apply lratCheckerSound f1228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1228
  · intro a ha; simp [p1228] at ha; subst a; trivial
  · exact checked1228
theorem derived1228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1228 := by
  apply localUnsat_implies_entails f1228 [c1221, c1189, c1125, c308, c1225, c1227, c23, c24, c15, c283, c61, c1226, c355, c116, c36, c210, c342] c1228 unsat1228 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c1225 := derived1225 a h
  have h5 : Entails.eval a c1227 := derived1227 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c1226 := derived1226 a h
  have h12 : Entails.eval a c355 := h 354 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1229 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1228, some c1221, some c1189, some c1125, some c31, some c268, some c601, some c470, some c9, some c251, some c703, some c516, some c311, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1229 : lratChecker f1229 p1229 = .success := by decide +kernel
theorem unsat1229 : Unsatisfiable (PosFin 31) f1229 := by
  apply lratCheckerSound f1229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1229
  · intro a ha; simp [p1229] at ha; subst a; trivial
  · exact checked1229
theorem derived1229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1229 := by
  apply localUnsat_implies_entails f1229 [c1228, c1221, c1189, c1125, c31, c268, c601, c470, c9, c251, c703, c516, c311] c1229 unsat1229 (by rfl) a
  have h0 : Entails.eval a c1228 := derived1228 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c601 := h 600 (by decide)
  have h7 : Entails.eval a c470 := h 469 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c703 := h 702 (by decide)
  have h11 : Entails.eval a c516 := h 515 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1230 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1228, some c1221, some c1189, some c1229, some c280, some c23, some c21, some c281, some c258, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1230 : lratChecker f1230 p1230 = .success := by decide +kernel
theorem unsat1230 : Unsatisfiable (PosFin 31) f1230 := by
  apply lratCheckerSound f1230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1230
  · intro a ha; simp [p1230] at ha; subst a; trivial
  · exact checked1230
theorem derived1230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1230 := by
  apply localUnsat_implies_entails f1230 [c1228, c1221, c1189, c1229, c280, c23, c21, c281, c258] c1230 unsat1230 (by rfl) a
  have h0 : Entails.eval a c1228 := derived1228 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1229 := derived1229 a h
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1231 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1228, some c1221, some c1189, some c1125, some c1230, some c55, some c262, some c182, some c489, some c61, some c1226, some c303, some c116, some c210, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1231 : lratChecker f1231 p1231 = .success := by decide +kernel
theorem unsat1231 : Unsatisfiable (PosFin 31) f1231 := by
  apply lratCheckerSound f1231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1231
  · intro a ha; simp [p1231] at ha; subst a; trivial
  · exact checked1231
theorem derived1231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1231 := by
  apply localUnsat_implies_entails f1231 [c1228, c1221, c1189, c1125, c1230, c55, c262, c182, c489, c61, c1226, c303, c116, c210] c1231 unsat1231 (by rfl) a
  have h0 : Entails.eval a c1228 := derived1228 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1230 := derived1230 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c489 := h 488 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c1226 := derived1226 a h
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1232 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1228, some c1189, some c262, some c7, some c258, some c22, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1232 : lratChecker f1232 p1232 = .success := by decide +kernel
theorem unsat1232 : Unsatisfiable (PosFin 31) f1232 := by
  apply lratCheckerSound f1232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1232
  · intro a ha; simp [p1232] at ha; subst a; trivial
  · exact checked1232
theorem derived1232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1232 := by
  apply localUnsat_implies_entails f1232 [c1228, c1189, c262, c7, c258, c22] c1232 unsat1232 (by rfl) a
  have h0 : Entails.eval a c1228 := derived1228 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1233 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1221, some c1189, some c1125, some c1231, some c24, some c1232, some c427, some c963, some c420, some c1081, some c777, some c601, some c780, some c642, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1233 : lratChecker f1233 p1233 = .success := by decide +kernel
theorem unsat1233 : Unsatisfiable (PosFin 31) f1233 := by
  apply lratCheckerSound f1233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1233
  · intro a ha; simp [p1233] at ha; subst a; trivial
  · exact checked1233
theorem derived1233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1233 := by
  apply localUnsat_implies_entails f1233 [c1221, c1189, c1125, c1231, c24, c1232, c427, c963, c420, c1081, c777, c601, c780, c642] c1233 unsat1233 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1231 := derived1231 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c1232 := derived1232 a h
  have h6 : Entails.eval a c427 := h 426 (by decide)
  have h7 : Entails.eval a c963 := derived963 a h
  have h8 : Entails.eval a c420 := h 419 (by decide)
  have h9 : Entails.eval a c1081 := derived1081 a h
  have h10 : Entails.eval a c777 := h 776 (by decide)
  have h11 : Entails.eval a c601 := h 600 (by decide)
  have h12 : Entails.eval a c780 := h 779 (by decide)
  have h13 : Entails.eval a c642 := h 641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1234 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1221, some c1189, some c1125, some c1233, some c71, some c304, some c60, some c61, some c23, some c24, some c18, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1234 : lratChecker f1234 p1234 = .success := by decide +kernel
theorem unsat1234 : Unsatisfiable (PosFin 31) f1234 := by
  apply lratCheckerSound f1234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1234
  · intro a ha; simp [p1234] at ha; subst a; trivial
  · exact checked1234
theorem derived1234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1234 := by
  apply localUnsat_implies_entails f1234 [c1221, c1189, c1125, c1233, c71, c304, c60, c61, c23, c24, c18] c1234 unsat1234 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c1233 := derived1233 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1235 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1234, some c1125, some c304, some c112, some c211, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1235 : lratChecker f1235 p1235 = .success := by decide +kernel
theorem unsat1235 : Unsatisfiable (PosFin 31) f1235 := by
  apply lratCheckerSound f1235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1235
  · intro a ha; simp [p1235] at ha; subst a; trivial
  · exact checked1235
theorem derived1235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1235 := by
  apply localUnsat_implies_entails f1235 [c1234, c1125, c304, c112, c211] c1235 unsat1235 (by rfl) a
  have h0 : Entails.eval a c1234 := derived1234 a h
  have h1 : Entails.eval a c1125 := derived1125 a h
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1236 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1235, some c1234, some c1228, some c1221, some c1125, some c31, some c553, some c1170, some c25, some c251, some c356, some c353, some c98, some c145, some c708, some c485, some c792, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1236 : lratChecker f1236 p1236 = .success := by decide +kernel
theorem unsat1236 : Unsatisfiable (PosFin 31) f1236 := by
  apply lratCheckerSound f1236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1236
  · intro a ha; simp [p1236] at ha; subst a; trivial
  · exact checked1236
theorem derived1236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1236 := by
  apply localUnsat_implies_entails f1236 [c1235, c1234, c1228, c1221, c1125, c31, c553, c1170, c25, c251, c356, c353, c98, c145, c708, c485, c792] c1236 unsat1236 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1234 := derived1234 a h
  have h2 : Entails.eval a c1228 := derived1228 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c553 := h 552 (by decide)
  have h7 : Entails.eval a c1170 := derived1170 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c145 := h 144 (by decide)
  have h14 : Entails.eval a c708 := h 707 (by decide)
  have h15 : Entails.eval a c485 := h 484 (by decide)
  have h16 : Entails.eval a c792 := h 791 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1237 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1234, some c1228, some c1221, some c1189, some c21, some c43, some c80, some c281, some c292, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1237 : lratChecker f1237 p1237 = .success := by decide +kernel
theorem unsat1237 : Unsatisfiable (PosFin 31) f1237 := by
  apply lratCheckerSound f1237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1237
  · intro a ha; simp [p1237] at ha; subst a; trivial
  · exact checked1237
theorem derived1237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1237 := by
  apply localUnsat_implies_entails f1237 [c1234, c1228, c1221, c1189, c21, c43, c80, c281, c292] c1237 unsat1237 (by rfl) a
  have h0 : Entails.eval a c1234 := derived1234 a h
  have h1 : Entails.eval a c1228 := derived1228 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1238 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1237, some c1235, some c1234, some c1221, some c1189, some c1125, some c1236, some c30, some c963, some c1170, some c406, some c223, some c731, some c323, some c893, some c45, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1238 : lratChecker f1238 p1238 = .success := by decide +kernel
theorem unsat1238 : Unsatisfiable (PosFin 31) f1238 := by
  apply lratCheckerSound f1238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1238
  · intro a ha; simp [p1238] at ha; subst a; trivial
  · exact checked1238
theorem derived1238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1238 := by
  apply localUnsat_implies_entails f1238 [c1237, c1235, c1234, c1221, c1189, c1125, c1236, c30, c963, c1170, c406, c223, c731, c323, c893, c45] c1238 unsat1238 (by rfl) a
  have h0 : Entails.eval a c1237 := derived1237 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1234 := derived1234 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1189 := derived1189 a h
  have h5 : Entails.eval a c1125 := derived1125 a h
  have h6 : Entails.eval a c1236 := derived1236 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c963 := derived963 a h
  have h9 : Entails.eval a c1170 := derived1170 a h
  have h10 : Entails.eval a c406 := h 405 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c731 := h 730 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c893 := h 892 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1239 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1235, some c1234, some c1189, some c1125, some c45, some c90, some c595, some c777, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1239 : lratChecker f1239 p1239 = .success := by decide +kernel
theorem unsat1239 : Unsatisfiable (PosFin 31) f1239 := by
  apply lratCheckerSound f1239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1239
  · intro a ha; simp [p1239] at ha; subst a; trivial
  · exact checked1239
theorem derived1239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1239 := by
  apply localUnsat_implies_entails f1239 [c1235, c1234, c1189, c1125, c45, c90, c595, c777] c1239 unsat1239 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1234 := derived1234 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c595 := h 594 (by decide)
  have h7 : Entails.eval a c777 := h 776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1240 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1238, some c1237, some c1235, some c1234, some c1228, some c1221, some c1189, some c1239, some c59, some c85, some c22, some c518, some c436, some c535, some c550, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1240 : lratChecker f1240 p1240 = .success := by decide +kernel
theorem unsat1240 : Unsatisfiable (PosFin 31) f1240 := by
  apply lratCheckerSound f1240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1240
  · intro a ha; simp [p1240] at ha; subst a; trivial
  · exact checked1240
theorem derived1240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1240 := by
  apply localUnsat_implies_entails f1240 [c1238, c1237, c1235, c1234, c1228, c1221, c1189, c1239, c59, c85, c22, c518, c436, c535, c550] c1240 unsat1240 (by rfl) a
  have h0 : Entails.eval a c1238 := derived1238 a h
  have h1 : Entails.eval a c1237 := derived1237 a h
  have h2 : Entails.eval a c1235 := derived1235 a h
  have h3 : Entails.eval a c1234 := derived1234 a h
  have h4 : Entails.eval a c1228 := derived1228 a h
  have h5 : Entails.eval a c1221 := derived1221 a h
  have h6 : Entails.eval a c1189 := derived1189 a h
  have h7 : Entails.eval a c1239 := derived1239 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c518 := h 517 (by decide)
  have h12 : Entails.eval a c436 := h 435 (by decide)
  have h13 : Entails.eval a c535 := h 534 (by decide)
  have h14 : Entails.eval a c550 := h 549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1241 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1235, some c1234, some c1228, some c1221, some c1125, some c1237, some c1238, some c1240, some c450, some c31, some c553, some c45, some c1170, some c25, some c808, some c564, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1241 : lratChecker f1241 p1241 = .success := by decide +kernel
theorem unsat1241 : Unsatisfiable (PosFin 31) f1241 := by
  apply lratCheckerSound f1241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1241
  · intro a ha; simp [p1241] at ha; subst a; trivial
  · exact checked1241
theorem derived1241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1241 := by
  apply localUnsat_implies_entails f1241 [c1235, c1234, c1228, c1221, c1125, c1237, c1238, c1240, c450, c31, c553, c45, c1170, c25, c808, c564] c1241 unsat1241 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1234 := derived1234 a h
  have h2 : Entails.eval a c1228 := derived1228 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1237 := derived1237 a h
  have h6 : Entails.eval a c1238 := derived1238 a h
  have h7 : Entails.eval a c1240 := derived1240 a h
  have h8 : Entails.eval a c450 := h 449 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c553 := h 552 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c1170 := derived1170 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c808 := h 807 (by decide)
  have h15 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1242 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1241, some c1235, some c1234, some c1228, some c1221, some c1189, some c59, some c85, some c488, some c384, some c518, some c963, some c363, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1242 : lratChecker f1242 p1242 = .success := by decide +kernel
theorem unsat1242 : Unsatisfiable (PosFin 31) f1242 := by
  apply lratCheckerSound f1242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1242
  · intro a ha; simp [p1242] at ha; subst a; trivial
  · exact checked1242
theorem derived1242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1242 := by
  apply localUnsat_implies_entails f1242 [c1241, c1235, c1234, c1228, c1221, c1189, c59, c85, c488, c384, c518, c963, c363] c1242 unsat1242 (by rfl) a
  have h0 : Entails.eval a c1241 := derived1241 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1234 := derived1234 a h
  have h3 : Entails.eval a c1228 := derived1228 a h
  have h4 : Entails.eval a c1221 := derived1221 a h
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c488 := h 487 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c518 := h 517 (by decide)
  have h11 : Entails.eval a c963 := derived963 a h
  have h12 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1243 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1235, some c1234, some c1228, some c1189, some c1125, some c1242, some c45, some c90, some c77, some c80, some c450, some c630, some c27, some c807, some c575, some c848, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1243 : lratChecker f1243 p1243 = .success := by decide +kernel
theorem unsat1243 : Unsatisfiable (PosFin 31) f1243 := by
  apply lratCheckerSound f1243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1243
  · intro a ha; simp [p1243] at ha; subst a; trivial
  · exact checked1243
theorem derived1243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1243 := by
  apply localUnsat_implies_entails f1243 [c1235, c1234, c1228, c1189, c1125, c1242, c45, c90, c77, c80, c450, c630, c27, c807, c575, c848] c1243 unsat1243 (by rfl) a
  have h0 : Entails.eval a c1235 := derived1235 a h
  have h1 : Entails.eval a c1234 := derived1234 a h
  have h2 : Entails.eval a c1228 := derived1228 a h
  have h3 : Entails.eval a c1189 := derived1189 a h
  have h4 : Entails.eval a c1125 := derived1125 a h
  have h5 : Entails.eval a c1242 := derived1242 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c450 := h 449 (by decide)
  have h11 : Entails.eval a c630 := h 629 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c807 := h 806 (by decide)
  have h14 : Entails.eval a c575 := h 574 (by decide)
  have h15 : Entails.eval a c848 := h 847 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1244 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1241, some c1235, some c1189, some c1243, some c1239, some c1232, some c85, some c595, some c777, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1244 : lratChecker f1244 p1244 = .success := by decide +kernel
theorem unsat1244 : Unsatisfiable (PosFin 31) f1244 := by
  apply lratCheckerSound f1244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1244
  · intro a ha; simp [p1244] at ha; subst a; trivial
  · exact checked1244
theorem derived1244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1244 := by
  apply localUnsat_implies_entails f1244 [c1241, c1235, c1189, c1243, c1239, c1232, c85, c595, c777] c1244 unsat1244 (by rfl) a
  have h0 : Entails.eval a c1241 := derived1241 a h
  have h1 : Entails.eval a c1235 := derived1235 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c1243 := derived1243 a h
  have h4 : Entails.eval a c1239 := derived1239 a h
  have h5 : Entails.eval a c1232 := derived1232 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c595 := h 594 (by decide)
  have h8 : Entails.eval a c777 := h 776 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1245 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1244, some c1241, some c1235, some c1234, some c1221, some c1189, some c1125, some c1232, some c406, some c963, some c401, some c620, some c622, some c577, some c801, some c213, some c731, some c43, some c729, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1245 : lratChecker f1245 p1245 = .success := by decide +kernel
theorem unsat1245 : Unsatisfiable (PosFin 31) f1245 := by
  apply lratCheckerSound f1245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1245
  · intro a ha; simp [p1245] at ha; subst a; trivial
  · exact checked1245
theorem derived1245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1245 := by
  apply localUnsat_implies_entails f1245 [c1244, c1241, c1235, c1234, c1221, c1189, c1125, c1232, c406, c963, c401, c620, c622, c577, c801, c213, c731, c43, c729] c1245 unsat1245 (by rfl) a
  have h0 : Entails.eval a c1244 := derived1244 a h
  have h1 : Entails.eval a c1241 := derived1241 a h
  have h2 : Entails.eval a c1235 := derived1235 a h
  have h3 : Entails.eval a c1234 := derived1234 a h
  have h4 : Entails.eval a c1221 := derived1221 a h
  have h5 : Entails.eval a c1189 := derived1189 a h
  have h6 : Entails.eval a c1125 := derived1125 a h
  have h7 : Entails.eval a c1232 := derived1232 a h
  have h8 : Entails.eval a c406 := h 405 (by decide)
  have h9 : Entails.eval a c963 := derived963 a h
  have h10 : Entails.eval a c401 := h 400 (by decide)
  have h11 : Entails.eval a c620 := h 619 (by decide)
  have h12 : Entails.eval a c622 := h 621 (by decide)
  have h13 : Entails.eval a c577 := h 576 (by decide)
  have h14 : Entails.eval a c801 := h 800 (by decide)
  have h15 : Entails.eval a c213 := h 212 (by decide)
  have h16 : Entails.eval a c731 := h 730 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c729 := h 728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1246 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1125, some c1189, some c1221, some c1228, some c1234, some c1235, some c1244, some c1245, some c1236, some c21, some c80, some c59, some c281, some c527, some c207, some c899, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1246 : lratChecker f1246 p1246 = .success := by decide +kernel
theorem unsat1246 : Unsatisfiable (PosFin 31) f1246 := by
  apply lratCheckerSound f1246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1246
  · intro a ha; simp [p1246] at ha; subst a; trivial
  · exact checked1246
theorem derived1246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1246 := by
  apply localUnsat_implies_entails f1246 [c1125, c1189, c1221, c1228, c1234, c1235, c1244, c1245, c1236, c21, c80, c59, c281, c527, c207, c899] c1246 unsat1246 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c1189 := derived1189 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1228 := derived1228 a h
  have h4 : Entails.eval a c1234 := derived1234 a h
  have h5 : Entails.eval a c1235 := derived1235 a h
  have h6 : Entails.eval a c1244 := derived1244 a h
  have h7 : Entails.eval a c1245 := derived1245 a h
  have h8 : Entails.eval a c1236 := derived1236 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c281 := h 280 (by decide)
  have h13 : Entails.eval a c527 := h 526 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c899 := h 898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1247 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c963, some c401, some c540, some c235, some c109, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1247 : lratChecker f1247 p1247 = .success := by decide +kernel
theorem unsat1247 : Unsatisfiable (PosFin 31) f1247 := by
  apply lratCheckerSound f1247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1247
  · intro a ha; simp [p1247] at ha; subst a; trivial
  · exact checked1247
theorem derived1247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1247 := by
  apply localUnsat_implies_entails f1247 [c1246, c963, c401, c540, c235, c109] c1247 unsat1247 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c401 := h 400 (by decide)
  have h3 : Entails.eval a c540 := h 539 (by decide)
  have h4 : Entails.eval a c235 := h 234 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1248 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c963, some c53, some c1247, some c453, some c31, some c145, some c180, some c25, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1248 : lratChecker f1248 p1248 = .success := by decide +kernel
theorem unsat1248 : Unsatisfiable (PosFin 31) f1248 := by
  apply lratCheckerSound f1248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1248
  · intro a ha; simp [p1248] at ha; subst a; trivial
  · exact checked1248
theorem derived1248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1248 := by
  apply localUnsat_implies_entails f1248 [c1246, c963, c53, c1247, c453, c31, c145, c180, c25] c1248 unsat1248 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c1247 := derived1247 a h
  have h4 : Entails.eval a c453 := h 452 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1249 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨28, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1248, some c27, some c52, some c31, some c9, some c843, some c188, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1249 : lratChecker f1249 p1249 = .success := by decide +kernel
theorem unsat1249 : Unsatisfiable (PosFin 31) f1249 := by
  apply lratCheckerSound f1249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1249
  · intro a ha; simp [p1249] at ha; subst a; trivial
  · exact checked1249
theorem derived1249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1249 := by
  apply localUnsat_implies_entails f1249 [c1246, c1248, c27, c52, c31, c9, c843, c188] c1249 unsat1249 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1248 := derived1248 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c843 := h 842 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1250 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c420, some c101, some c31, some c251, some c601, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1250 : lratChecker f1250 p1250 = .success := by decide +kernel
theorem unsat1250 : Unsatisfiable (PosFin 31) f1250 := by
  apply lratCheckerSound f1250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1250
  · intro a ha; simp [p1250] at ha; subst a; trivial
  · exact checked1250
theorem derived1250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1250 := by
  apply localUnsat_implies_entails f1250 [c420, c101, c31, c251, c601] c1250 unsat1250 (by rfl) a
  have h0 : Entails.eval a c420 := h 419 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c601 := h 600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1251 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1249, some c1250, some c963, some c1247, some c53, some c453, some c31, some c9, some c147, some c888, some c314, some c490, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1251 : lratChecker f1251 p1251 = .success := by decide +kernel
theorem unsat1251 : Unsatisfiable (PosFin 31) f1251 := by
  apply lratCheckerSound f1251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1251
  · intro a ha; simp [p1251] at ha; subst a; trivial
  · exact checked1251
theorem derived1251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1251 := by
  apply localUnsat_implies_entails f1251 [c1246, c1249, c1250, c963, c1247, c53, c453, c31, c9, c147, c888, c314, c490] c1251 unsat1251 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1249 := derived1249 a h
  have h2 : Entails.eval a c1250 := derived1250 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c1247 := derived1247 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c453 := h 452 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c888 := h 887 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c490 := h 489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1252 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1251, some c6, some c328, some c453, some c31, some c9, some c145, some c601, some c337, some c690, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1252 : lratChecker f1252 p1252 = .success := by decide +kernel
theorem unsat1252 : Unsatisfiable (PosFin 31) f1252 := by
  apply lratCheckerSound f1252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1252
  · intro a ha; simp [p1252] at ha; subst a; trivial
  · exact checked1252
theorem derived1252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1252 := by
  apply localUnsat_implies_entails f1252 [c1246, c1251, c6, c328, c453, c31, c9, c145, c601, c337, c690] c1252 unsat1252 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c453 := h 452 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c601 := h 600 (by decide)
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c690 := h 689 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1253 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1251, some c328, some c53, some c6, some c1252, some c401, some c548, some c1205, some c385, some c758, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1253 : lratChecker f1253 p1253 = .success := by decide +kernel
theorem unsat1253 : Unsatisfiable (PosFin 31) f1253 := by
  apply lratCheckerSound f1253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1253
  · intro a ha; simp [p1253] at ha; subst a; trivial
  · exact checked1253
theorem derived1253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1253 := by
  apply localUnsat_implies_entails f1253 [c1246, c1251, c328, c53, c6, c1252, c401, c548, c1205, c385, c758] c1253 unsat1253 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1252 := derived1252 a h
  have h6 : Entails.eval a c401 := h 400 (by decide)
  have h7 : Entails.eval a c548 := h 547 (by decide)
  have h8 : Entails.eval a c1205 := derived1205 a h
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c758 := h 757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1254 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1251, some c328, some c1253, some c963, some c29, some c1250, some c453, some c256, some c145, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1254 : lratChecker f1254 p1254 = .success := by decide +kernel
theorem unsat1254 : Unsatisfiable (PosFin 31) f1254 := by
  apply lratCheckerSound f1254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1254
  · intro a ha; simp [p1254] at ha; subst a; trivial
  · exact checked1254
theorem derived1254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1254 := by
  apply localUnsat_implies_entails f1254 [c1246, c1251, c328, c1253, c963, c29, c1250, c453, c256, c145] c1254 unsat1254 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1251 := derived1251 a h
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c1253 := derived1253 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1250 := derived1250 a h
  have h7 : Entails.eval a c453 := h 452 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1255 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c438, some c626, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1255 : lratChecker f1255 p1255 = .success := by decide +kernel
theorem unsat1255 : Unsatisfiable (PosFin 31) f1255 := by
  apply lratCheckerSound f1255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1255
  · intro a ha; simp [p1255] at ha; subst a; trivial
  · exact checked1255
theorem derived1255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1255 := by
  apply localUnsat_implies_entails f1255 [c1246, c438, c626] c1255 unsat1255 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c438 := h 437 (by decide)
  have h2 : Entails.eval a c626 := h 625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1256 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c453, some c31, some c147, some c1255, some c490, some c385, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1256 : lratChecker f1256 p1256 = .success := by decide +kernel
theorem unsat1256 : Unsatisfiable (PosFin 31) f1256 := by
  apply lratCheckerSound f1256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1256
  · intro a ha; simp [p1256] at ha; subst a; trivial
  · exact checked1256
theorem derived1256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1256 := by
  apply localUnsat_implies_entails f1256 [c1246, c453, c31, c147, c1255, c490, c385] c1256 unsat1256 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c453 := h 452 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c1255 := derived1255 a h
  have h5 : Entails.eval a c490 := h 489 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1257 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c147, some c385, some c490, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1257 : lratChecker f1257 p1257 = .success := by decide +kernel
theorem unsat1257 : Unsatisfiable (PosFin 31) f1257 := by
  apply lratCheckerSound f1257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1257
  · intro a ha; simp [p1257] at ha; subst a; trivial
  · exact checked1257
theorem derived1257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1257 := by
  apply localUnsat_implies_entails f1257 [c1246, c147, c385, c490] c1257 unsat1257 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c490 := h 489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1258 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c509, some c694, some c212, some c70, some c585, some c963, some c359, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1258 : lratChecker f1258 p1258 = .success := by decide +kernel
theorem unsat1258 : Unsatisfiable (PosFin 31) f1258 := by
  apply lratCheckerSound f1258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1258
  · intro a ha; simp [p1258] at ha; subst a; trivial
  · exact checked1258
theorem derived1258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1258 := by
  apply localUnsat_implies_entails f1258 [c1246, c509, c694, c212, c70, c585, c963, c359] c1258 unsat1258 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c509 := h 508 (by decide)
  have h2 : Entails.eval a c694 := h 693 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c585 := h 584 (by decide)
  have h6 : Entails.eval a c963 := derived963 a h
  have h7 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1259 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1257, some c576, some c1258, some c1205, some c94, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1259 : lratChecker f1259 p1259 = .success := by decide +kernel
theorem unsat1259 : Unsatisfiable (PosFin 31) f1259 := by
  apply lratCheckerSound f1259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1259
  · intro a ha; simp [p1259] at ha; subst a; trivial
  · exact checked1259
theorem derived1259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1259 := by
  apply localUnsat_implies_entails f1259 [c1246, c1257, c576, c1258, c1205, c94] c1259 unsat1259 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1257 := derived1257 a h
  have h2 : Entails.eval a c576 := h 575 (by decide)
  have h3 : Entails.eval a c1258 := derived1258 a h
  have h4 : Entails.eval a c1205 := derived1205 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1260 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1254, some c1256, some c1259, some c540, some c404, some c59, some c278, some c416, some c548, some c6, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1260 : lratChecker f1260 p1260 = .success := by decide +kernel
theorem unsat1260 : Unsatisfiable (PosFin 31) f1260 := by
  apply lratCheckerSound f1260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1260
  · intro a ha; simp [p1260] at ha; subst a; trivial
  · exact checked1260
theorem derived1260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1260 := by
  apply localUnsat_implies_entails f1260 [c1246, c1254, c1256, c1259, c540, c404, c59, c278, c416, c548, c6] c1260 unsat1260 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1256 := derived1256 a h
  have h3 : Entails.eval a c1259 := derived1259 a h
  have h4 : Entails.eval a c540 := h 539 (by decide)
  have h5 : Entails.eval a c404 := h 403 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c416 := h 415 (by decide)
  have h9 : Entails.eval a c548 := h 547 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1261 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨20, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c79, some c580, some c127, some c1113, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1261 : lratChecker f1261 p1261 = .success := by decide +kernel
theorem unsat1261 : Unsatisfiable (PosFin 31) f1261 := by
  apply lratCheckerSound f1261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1261
  · intro a ha; simp [p1261] at ha; subst a; trivial
  · exact checked1261
theorem derived1261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1261 := by
  apply localUnsat_implies_entails f1261 [c1246, c79, c580, c127, c1113] c1261 unsat1261 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c580 := h 579 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c1113 := derived1113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1262 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c404, some c967, some c580, some c259, some c52, some c314, some c93, some c544, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1262 : lratChecker f1262 p1262 = .success := by decide +kernel
theorem unsat1262 : Unsatisfiable (PosFin 31) f1262 := by
  apply lratCheckerSound f1262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1262
  · intro a ha; simp [p1262] at ha; subst a; trivial
  · exact checked1262
theorem derived1262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1262 := by
  apply localUnsat_implies_entails f1262 [c1246, c404, c967, c580, c259, c52, c314, c93, c544] c1262 unsat1262 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c404 := h 403 (by decide)
  have h2 : Entails.eval a c967 := derived967 a h
  have h3 : Entails.eval a c580 := h 579 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c544 := h 543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1263 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨28, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1262, some c79, some c1261, some c580, some c147, some c634, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1263 : lratChecker f1263 p1263 = .success := by decide +kernel
theorem unsat1263 : Unsatisfiable (PosFin 31) f1263 := by
  apply lratCheckerSound f1263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1263
  · intro a ha; simp [p1263] at ha; subst a; trivial
  · exact checked1263
theorem derived1263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1263 := by
  apply localUnsat_implies_entails f1263 [c1246, c1262, c79, c1261, c580, c147, c634] c1263 unsat1263 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1262 := derived1262 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1261 := derived1261 a h
  have h4 : Entails.eval a c580 := h 579 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c634 := h 633 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1264 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1260, some c1263, some c1257, some c576, some c453, some c1259, some c789, some c616, some c328, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1264 : lratChecker f1264 p1264 = .success := by decide +kernel
theorem unsat1264 : Unsatisfiable (PosFin 31) f1264 := by
  apply lratCheckerSound f1264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1264
  · intro a ha; simp [p1264] at ha; subst a; trivial
  · exact checked1264
theorem derived1264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1264 := by
  apply localUnsat_implies_entails f1264 [c1246, c1260, c1263, c1257, c576, c453, c1259, c789, c616, c328] c1264 unsat1264 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1260 := derived1260 a h
  have h2 : Entails.eval a c1263 := derived1263 a h
  have h3 : Entails.eval a c1257 := derived1257 a h
  have h4 : Entails.eval a c576 := h 575 (by decide)
  have h5 : Entails.eval a c453 := h 452 (by decide)
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c789 := h 788 (by decide)
  have h8 : Entails.eval a c616 := h 615 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1265 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c493, some c759, some c312, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1265 : lratChecker f1265 p1265 = .success := by decide +kernel
theorem unsat1265 : Unsatisfiable (PosFin 31) f1265 := by
  apply lratCheckerSound f1265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1265
  · intro a ha; simp [p1265] at ha; subst a; trivial
  · exact checked1265
theorem derived1265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1265 := by
  apply localUnsat_implies_entails f1265 [c1246, c493, c759, c312] c1265 unsat1265 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c493 := h 492 (by decide)
  have h2 : Entails.eval a c759 := h 758 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1266 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1264, some c1257, some c576, some c453, some c1259, some c1265, some c490, some c1205, some c94, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1266 : lratChecker f1266 p1266 = .success := by decide +kernel
theorem unsat1266 : Unsatisfiable (PosFin 31) f1266 := by
  apply lratCheckerSound f1266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1266
  · intro a ha; simp [p1266] at ha; subst a; trivial
  · exact checked1266
theorem derived1266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1266 := by
  apply localUnsat_implies_entails f1266 [c1246, c1264, c1257, c576, c453, c1259, c1265, c490, c1205, c94] c1266 unsat1266 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1264 := derived1264 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c576 := h 575 (by decide)
  have h4 : Entails.eval a c453 := h 452 (by decide)
  have h5 : Entails.eval a c1259 := derived1259 a h
  have h6 : Entails.eval a c1265 := derived1265 a h
  have h7 : Entails.eval a c490 := h 489 (by decide)
  have h8 : Entails.eval a c1205 := derived1205 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1267 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1266, some c1263, some c1256, some c404, some c540, some c36, some c328, some c6, some c417, some c524, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1267 : lratChecker f1267 p1267 = .success := by decide +kernel
theorem unsat1267 : Unsatisfiable (PosFin 31) f1267 := by
  apply lratCheckerSound f1267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1267
  · intro a ha; simp [p1267] at ha; subst a; trivial
  · exact checked1267
theorem derived1267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1267 := by
  apply localUnsat_implies_entails f1267 [c1246, c1266, c1263, c1256, c404, c540, c36, c328, c6, c417, c524] c1267 unsat1267 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c1263 := derived1263 a h
  have h3 : Entails.eval a c1256 := derived1256 a h
  have h4 : Entails.eval a c404 := h 403 (by decide)
  have h5 : Entails.eval a c540 := h 539 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c417 := h 416 (by decide)
  have h10 : Entails.eval a c524 := h 523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1268 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1263, some c1256, some c59, some c540, some c404, some c1267, some c46, some c278, some c52, some c524, some c88, some c1113, some c785, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1268 : lratChecker f1268 p1268 = .success := by decide +kernel
theorem unsat1268 : Unsatisfiable (PosFin 31) f1268 := by
  apply lratCheckerSound f1268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1268
  · intro a ha; simp [p1268] at ha; subst a; trivial
  · exact checked1268
theorem derived1268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1268 := by
  apply localUnsat_implies_entails f1268 [c1246, c1263, c1256, c59, c540, c404, c1267, c46, c278, c52, c524, c88, c1113, c785] c1268 unsat1268 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1263 := derived1263 a h
  have h2 : Entails.eval a c1256 := derived1256 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c540 := h 539 (by decide)
  have h5 : Entails.eval a c404 := h 403 (by decide)
  have h6 : Entails.eval a c1267 := derived1267 a h
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c524 := h 523 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c1113 := derived1113 a h
  have h13 : Entails.eval a c785 := h 784 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1269 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1266, some c1268, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1269 : lratChecker f1269 p1269 = .success := by decide +kernel
theorem unsat1269 : Unsatisfiable (PosFin 31) f1269 := by
  apply lratCheckerSound f1269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1269
  · intro a ha; simp [p1269] at ha; subst a; trivial
  · exact checked1269
theorem derived1269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1269 := by
  apply localUnsat_implies_entails f1269 [c1266, c1268] c1269 unsat1269 (by rfl) a
  have h0 : Entails.eval a c1266 := derived1266 a h
  have h1 : Entails.eval a c1268 := derived1268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1270 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c963, some c1113, some c53, some c371, some c542, some c724, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1270 : lratChecker f1270 p1270 = .success := by decide +kernel
theorem unsat1270 : Unsatisfiable (PosFin 31) f1270 := by
  apply lratCheckerSound f1270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1270
  · intro a ha; simp [p1270] at ha; subst a; trivial
  · exact checked1270
theorem derived1270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1270 := by
  apply localUnsat_implies_entails f1270 [c1246, c1269, c963, c1113, c53, c371, c542, c724] c1270 unsat1270 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c1113 := derived1113 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c542 := h 541 (by decide)
  have h7 : Entails.eval a c724 := h 723 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1271 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c52, some c313, some c209, some c121, some c316, some c495, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1271 : lratChecker f1271 p1271 = .success := by decide +kernel
theorem unsat1271 : Unsatisfiable (PosFin 31) f1271 := by
  apply lratCheckerSound f1271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1271
  · intro a ha; simp [p1271] at ha; subst a; trivial
  · exact checked1271
theorem derived1271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1271 := by
  apply localUnsat_implies_entails f1271 [c1246, c52, c313, c209, c121, c316, c495] c1271 unsat1271 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c495 := h 494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1272 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨23, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c1270, some c52, some c274, some c1271, some c46, some c53, some c38, some c388, some c71, some c336, some c749, some c360, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1272 : lratChecker f1272 p1272 = .success := by decide +kernel
theorem unsat1272 : Unsatisfiable (PosFin 31) f1272 := by
  apply lratCheckerSound f1272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1272
  · intro a ha; simp [p1272] at ha; subst a; trivial
  · exact checked1272
theorem derived1272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1272 := by
  apply localUnsat_implies_entails f1272 [c1246, c1269, c1270, c52, c274, c1271, c46, c53, c38, c388, c71, c336, c749, c360] c1272 unsat1272 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c1270 := derived1270 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c1271 := derived1271 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c749 := h 748 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1273 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1270, some c52, some c274, some c1272, some c260, some c261, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1273 : lratChecker f1273 p1273 = .success := by decide +kernel
theorem unsat1273 : Unsatisfiable (PosFin 31) f1273 := by
  apply lratCheckerSound f1273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1273
  · intro a ha; simp [p1273] at ha; subst a; trivial
  · exact checked1273
theorem derived1273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1273 := by
  apply localUnsat_implies_entails f1273 [c1246, c1270, c52, c274, c1272, c260, c261] c1273 unsat1273 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1270 := derived1270 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c1272 := derived1272 a h
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1274 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c9, some c29, some c1273, some c265, some c1269, some c1271, some c261, some c278, some c6, some c279, some c152, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1274 : lratChecker f1274 p1274 = .success := by decide +kernel
theorem unsat1274 : Unsatisfiable (PosFin 31) f1274 := by
  apply lratCheckerSound f1274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1274
  · intro a ha; simp [p1274] at ha; subst a; trivial
  · exact checked1274
theorem derived1274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1274 := by
  apply localUnsat_implies_entails f1274 [c9, c29, c1273, c265, c1269, c1271, c261, c278, c6, c279, c152] c1274 unsat1274 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c1273 := derived1273 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c1269 := derived1269 a h
  have h5 : Entails.eval a c1271 := derived1271 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c279 := h 278 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1275 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1273, some c1269, some c9, some c1274, some c307, some c226, some c694, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1275 : lratChecker f1275 p1275 = .success := by decide +kernel
theorem unsat1275 : Unsatisfiable (PosFin 31) f1275 := by
  apply lratCheckerSound f1275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1275
  · intro a ha; simp [p1275] at ha; subst a; trivial
  · exact checked1275
theorem derived1275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1275 := by
  apply localUnsat_implies_entails f1275 [c1246, c1273, c1269, c9, c1274, c307, c226, c694] c1275 unsat1275 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1273 := derived1273 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1274 := derived1274 a h
  have h5 : Entails.eval a c307 := h 306 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1276 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c71, some c31, some c228, some c530, some c694, some c835, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1276 : lratChecker f1276 p1276 = .success := by decide +kernel
theorem unsat1276 : Unsatisfiable (PosFin 31) f1276 := by
  apply lratCheckerSound f1276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1276
  · intro a ha; simp [p1276] at ha; subst a; trivial
  · exact checked1276
theorem derived1276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1276 := by
  apply localUnsat_implies_entails f1276 [c1246, c1269, c71, c31, c228, c530, c694, c835] c1276 unsat1276 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c530 := h 529 (by decide)
  have h6 : Entails.eval a c694 := h 693 (by decide)
  have h7 : Entails.eval a c835 := h 834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1277 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1273, some c1269, some c1275, some c38, some c71, some c1276, some c1271, some c335, some c302, some c336, some c33, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1277 : lratChecker f1277 p1277 = .success := by decide +kernel
theorem unsat1277 : Unsatisfiable (PosFin 31) f1277 := by
  apply lratCheckerSound f1277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1277
  · intro a ha; simp [p1277] at ha; subst a; trivial
  · exact checked1277
theorem derived1277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1277 := by
  apply localUnsat_implies_entails f1277 [c1246, c1273, c1269, c1275, c38, c71, c1276, c1271, c335, c302, c336, c33] c1277 unsat1277 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1273 := derived1273 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1276 := derived1276 a h
  have h7 : Entails.eval a c1271 := derived1271 a h
  have h8 : Entails.eval a c335 := h 334 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  have h10 : Entails.eval a c336 := h 335 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1278 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c53, some c265, some c261, some c197, some c861, some c869, some c505, some c865, some c867, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1278 : lratChecker f1278 p1278 = .success := by decide +kernel
theorem unsat1278 : Unsatisfiable (PosFin 31) f1278 := by
  apply lratCheckerSound f1278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1278
  · intro a ha; simp [p1278] at ha; subst a; trivial
  · exact checked1278
theorem derived1278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1278 := by
  apply localUnsat_implies_entails f1278 [c1246, c53, c265, c261, c197, c861, c869, c505, c865, c867] c1278 unsat1278 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c861 := h 860 (by decide)
  have h6 : Entails.eval a c869 := h 868 (by decide)
  have h7 : Entails.eval a c505 := h 504 (by decide)
  have h8 : Entails.eval a c865 := h 864 (by decide)
  have h9 : Entails.eval a c867 := h 866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1279 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1273, some c1269, some c1277, some c963, some c53, some c9, some c1278, some c307, some c694, some c211, some c321, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1279 : lratChecker f1279 p1279 = .success := by decide +kernel
theorem unsat1279 : Unsatisfiable (PosFin 31) f1279 := by
  apply lratCheckerSound f1279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1279
  · intro a ha; simp [p1279] at ha; subst a; trivial
  · exact checked1279
theorem derived1279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1279 := by
  apply localUnsat_implies_entails f1279 [c1246, c1273, c1269, c1277, c963, c53, c9, c1278, c307, c694, c211, c321] c1279 unsat1279 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1273 := derived1273 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c694 := h 693 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1280 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c325, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1280 : lratChecker f1280 p1280 = .success := by decide +kernel
theorem unsat1280 : Unsatisfiable (PosFin 31) f1280 := by
  apply lratCheckerSound f1280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1280
  · intro a ha; simp [p1280] at ha; subst a; trivial
  · exact checked1280
theorem derived1280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1280 := by
  apply localUnsat_implies_entails f1280 [c225, c325] c1280 unsat1280 (by rfl) a
  have h0 : Entails.eval a c225 := h 224 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1281 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c725, some c544, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1281 : lratChecker f1281 p1281 = .success := by decide +kernel
theorem unsat1281 : Unsatisfiable (PosFin 31) f1281 := by
  apply lratCheckerSound f1281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1281
  · intro a ha; simp [p1281] at ha; subst a; trivial
  · exact checked1281
theorem derived1281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1281 := by
  apply localUnsat_implies_entails f1281 [c1246, c725, c544] c1281 unsat1281 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c725 := h 724 (by decide)
  have h2 : Entails.eval a c544 := h 543 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1282 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c13, some c317, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1282 : lratChecker f1282 p1282 = .success := by decide +kernel
theorem unsat1282 : Unsatisfiable (PosFin 31) f1282 := by
  apply lratCheckerSound f1282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1282
  · intro a ha; simp [p1282] at ha; subst a; trivial
  · exact checked1282
theorem derived1282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1282 := by
  apply localUnsat_implies_entails f1282 [c71, c13, c317] c1282 unsat1282 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1283 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c1273, some c1279, some c52, some c963, some c53, some c1280, some c1281, some c215, some c6, some c1282, some c505, some c1255, some c555, some c484, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1283 : lratChecker f1283 p1283 = .success := by decide +kernel
theorem unsat1283 : Unsatisfiable (PosFin 31) f1283 := by
  apply lratCheckerSound f1283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1283
  · intro a ha; simp [p1283] at ha; subst a; trivial
  · exact checked1283
theorem derived1283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1283 := by
  apply localUnsat_implies_entails f1283 [c1246, c1269, c1273, c1279, c52, c963, c53, c1280, c1281, c215, c6, c1282, c505, c1255, c555, c484] c1283 unsat1283 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c1273 := derived1273 a h
  have h3 : Entails.eval a c1279 := derived1279 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c1280 := derived1280 a h
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c1282 := derived1282 a h
  have h12 : Entails.eval a c505 := h 504 (by decide)
  have h13 : Entails.eval a c1255 := derived1255 a h
  have h14 : Entails.eval a c555 := h 554 (by decide)
  have h15 : Entails.eval a c484 := h 483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1284 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1283, some c1269, some c52, some c963, some c1270, some c1280, some c53, some c1281, some c215, some c68, some c306, some c6, some c821, some c1282, some c176, some c96, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1284 : lratChecker f1284 p1284 = .success := by decide +kernel
theorem unsat1284 : Unsatisfiable (PosFin 31) f1284 := by
  apply lratCheckerSound f1284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1284
  · intro a ha; simp [p1284] at ha; subst a; trivial
  · exact checked1284
theorem derived1284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1284 := by
  apply localUnsat_implies_entails f1284 [c1246, c1283, c1269, c52, c963, c1270, c1280, c53, c1281, c215, c68, c306, c6, c821, c1282, c176, c96] c1284 unsat1284 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c1270 := derived1270 a h
  have h6 : Entails.eval a c1280 := derived1280 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c821 := h 820 (by decide)
  have h14 : Entails.eval a c1282 := derived1282 a h
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1285 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c963, some c53, some c54, some c9, some c1270, some c1269, some c261, some c1281, some c197, some c68, some c865, some c861, some c859, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1285 : lratChecker f1285 p1285 = .success := by decide +kernel
theorem unsat1285 : Unsatisfiable (PosFin 31) f1285 := by
  apply lratCheckerSound f1285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1285
  · intro a ha; simp [p1285] at ha; subst a; trivial
  · exact checked1285
theorem derived1285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1285 := by
  apply localUnsat_implies_entails f1285 [c1246, c963, c53, c54, c9, c1270, c1269, c261, c1281, c197, c68, c865, c861, c859] c1285 unsat1285 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1270 := derived1270 a h
  have h6 : Entails.eval a c1269 := derived1269 a h
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c865 := h 864 (by decide)
  have h12 : Entails.eval a c861 := h 860 (by decide)
  have h13 : Entails.eval a c859 := h 858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1286 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1284, some c1283, some c1269, some c963, some c1270, some c53, some c9, some c54, some c157, some c1285, some c225, some c307, some c544, some c694, some c331, some c71, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1286 : lratChecker f1286 p1286 = .success := by decide +kernel
theorem unsat1286 : Unsatisfiable (PosFin 31) f1286 := by
  apply lratCheckerSound f1286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1286
  · intro a ha; simp [p1286] at ha; subst a; trivial
  · exact checked1286
theorem derived1286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1286 := by
  apply localUnsat_implies_entails f1286 [c1246, c1284, c1283, c1269, c963, c1270, c53, c9, c54, c157, c1285, c225, c307, c544, c694, c331, c71] c1286 unsat1286 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1284 := derived1284 a h
  have h2 : Entails.eval a c1283 := derived1283 a h
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c1270 := derived1270 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c1285 := derived1285 a h
  have h11 : Entails.eval a c225 := h 224 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  have h13 : Entails.eval a c544 := h 543 (by decide)
  have h14 : Entails.eval a c694 := h 693 (by decide)
  have h15 : Entails.eval a c331 := h 330 (by decide)
  have h16 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1287 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1286, some c1284, some c1269, some c31, some c274, some c226, some c29, some c694, some c10, some c307, some c38, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1287 : lratChecker f1287 p1287 = .success := by decide +kernel
theorem unsat1287 : Unsatisfiable (PosFin 31) f1287 := by
  apply lratCheckerSound f1287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1287
  · intro a ha; simp [p1287] at ha; subst a; trivial
  · exact checked1287
theorem derived1287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1287 := by
  apply localUnsat_implies_entails f1287 [c1246, c1286, c1284, c1269, c31, c274, c226, c29, c694, c10, c307, c38] c1287 unsat1287 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1286 := derived1286 a h
  have h2 : Entails.eval a c1284 := derived1284 a h
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c694 := h 693 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1288 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c38, some c71, some c1287, some c1286, some c1284, some c1283, some c1281, some c315, some c302, some c335, some c673, some c354, some c283, some c717, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1288 : lratChecker f1288 p1288 = .success := by decide +kernel
theorem unsat1288 : Unsatisfiable (PosFin 31) f1288 := by
  apply lratCheckerSound f1288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1288
  · intro a ha; simp [p1288] at ha; subst a; trivial
  · exact checked1288
theorem derived1288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1288 := by
  apply localUnsat_implies_entails f1288 [c1246, c1269, c38, c71, c1287, c1286, c1284, c1283, c1281, c315, c302, c335, c673, c354, c283, c717] c1288 unsat1288 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c1286 := derived1286 a h
  have h6 : Entails.eval a c1284 := derived1284 a h
  have h7 : Entails.eval a c1283 := derived1283 a h
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c673 := h 672 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c717 := h 716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1289 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1287, some c1286, some c1284, some c1283, some c1269, some c53, some c38, some c71, some c1288, some c142, some c787, some c783, some c121, some c388, some c837, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 31) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c1246, c1287, c1286, c1284, c1283, c1269, c53, c38, c71, c1288, c142, c787, c783, c121, c388, c837] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c1286 := derived1286 a h
  have h3 : Entails.eval a c1284 := derived1284 a h
  have h4 : Entails.eval a c1283 := derived1283 a h
  have h5 : Entails.eval a c1269 := derived1269 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c1288 := derived1288 a h
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c787 := h 786 (by decide)
  have h12 : Entails.eval a c783 := h 782 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c388 := h 387 (by decide)
  have h15 : Entails.eval a c837 := h 836 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1269, some c1284, some c1287, some c1289, some c9, some c54, some c261, some c260, some c197, some c1281, some c861, some c306, some c694, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 31) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c1246, c1269, c1284, c1287, c1289, c9, c54, c261, c260, c197, c1281, c861, c306, c694] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c1284 := derived1284 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1289 := derived1289 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c1281 := derived1281 a h
  have h11 : Entails.eval a c861 := h 860 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1290, some c1257, some c576, some c260, some c197, some c1281, some c208, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 31) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c1246, c1290, c1257, c576, c260, c197, c1281, c208] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1290 := derived1290 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c576 := h 575 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c1281 := derived1281 a h
  have h7 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1290, some c1257, some c576, some c1291, some c53, some c94, some c1281, some c208, some c135, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 31) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c1246, c1290, c1257, c576, c1291, c53, c94, c1281, c208, c135] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1290 := derived1290 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c576 := h 575 (by decide)
  have h4 : Entails.eval a c1291 := derived1291 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c1281 := derived1281 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1290, some c1292, some c31, some c274, some c12, some c509, some c694, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 31) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c1246, c1290, c1292, c31, c274, c12, c509, c694] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1290 := derived1290 a h
  have h2 : Entails.eval a c1292 := derived1292 a h
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c509 := h 508 (by decide)
  have h7 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1290, some c1293, some c52, some c207, some c1270, some c1280, some c208, some c1281, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 31) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c1246, c1290, c1293, c52, c207, c1270, c1280, c208, c1281] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1290 := derived1290 a h
  have h2 : Entails.eval a c1293 := derived1293 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c1270 := derived1270 a h
  have h6 : Entails.eval a c1280 := derived1280 a h
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c1281 := derived1281 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1294, some c442, some c725, some c32, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 31) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c1246, c1294, c442, c725, c32] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1294 := derived1294 a h
  have h2 : Entails.eval a c442 := h 441 (by decide)
  have h3 : Entails.eval a c725 := h 724 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c963, some c53, some c1294, some c213, some c208, some c143, some c597, some c409, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 31) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c1246, c963, c53, c1294, c213, c208, c143, c597, c409] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c597 := h 596 (by decide)
  have h8 : Entails.eval a c409 := h 408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c480, some c167, some c669, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 31) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c480, c167, c669] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c480 := h 479 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c669 := h 668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c52, some c963, some c53, some c1294, some c30, some c1296, some c37, some c1295, some c1297, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 31) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c1246, c52, c963, c53, c1294, c30, c1296, c37, c1295, c1297] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c1294 := derived1294 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1296 := derived1296 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c1295 := derived1295 a h
  have h9 : Entails.eval a c1297 := derived1297 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1298, some c52, some c963, some c53, some c1294, some c30, some c167, some c109, some c1297, some c734, some c440, some c37, some c496, some c339, some c728, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 31) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c1246, c1298, c52, c963, c53, c1294, c30, c167, c109, c1297, c734, c440, c37, c496, c339, c728] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c1294 := derived1294 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c1297 := derived1297 a h
  have h10 : Entails.eval a c734 := h 733 (by decide)
  have h11 : Entails.eval a c440 := h 439 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c496 := h 495 (by decide)
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c728 := h 727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1299, some c1298, some c1294, some c52, some c963, some c30, some c532, some c37, some c147, some c728, some c301, some c389, some c339, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 31) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c1246, c1299, c1298, c1294, c52, c963, c30, c532, c37, c147, c728, c301, c389, c339] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c532 := h 531 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c728 := h 727 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1298, some c301, some c1294, some c52, some c963, some c30, some c1300, some c10, some c1299, some c339, some c637, some c291, some c289, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 31) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c1246, c1298, c301, c1294, c52, c963, c30, c1300, c10, c1299, c339, c637, c291, c289] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c1294 := derived1294 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1300 := derived1300 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1299 := derived1299 a h
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c637 := h 636 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1298, some c1294, some c52, some c963, some c30, some c1300, some c10, some c1299, some c53, some c1301, some c728, some c320, some c98, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 31) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c1246, c1298, c1294, c52, c963, c30, c1300, c10, c1299, c53, c1301, c728, c320, c98] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c963 := derived963 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1300 := derived1300 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1299 := derived1299 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c1301 := derived1301 a h
  have h11 : Entails.eval a c728 := h 727 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1302

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
