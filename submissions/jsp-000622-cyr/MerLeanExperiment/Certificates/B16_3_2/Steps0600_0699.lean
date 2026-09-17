import MerLeanExperiment.Certificates.B16_3_2.Steps0500_0599

/-! Generated from the actual pinned b16_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c999 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨32, by decide⟩, true), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c998, some c997, some c8, some c126, some c134, some c301, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c998, c997, c8, c126, c134, c301] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, true), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false), (⟨33, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c8, some c154, some c172, some c331, some c696, some c228, some c278, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c898, c8, c154, c172, c331, c696, c228, c278] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c696 := derived696 a h
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c996, some c45, some c328, some c972, some c25, some c85, some c30, some c921, some c898, some c120, some c74, some c94, some c38, some c999, some c236, some c279, some c1000, some c140, some c997, some c278, some c6, some c993, some c172, some c381, some c194, some c196, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c22, c996, c45, c328, c972, c25, c85, c30, c921, c898, c120, c74, c94, c38, c999, c236, c279, c1000, c140, c997, c278, c6, c993, c172, c381, c194, c196] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c996 := derived996 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c972 := derived972 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c921 := derived921 a h
  have h9 : Entails.eval a c898 := derived898 a h
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c999 := derived999 a h
  have h15 : Entails.eval a c236 := h 235 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c1000 := derived1000 a h
  have h18 : Entails.eval a c140 := h 139 (by decide)
  have h19 : Entails.eval a c997 := derived997 a h
  have h20 : Entails.eval a c278 := h 277 (by decide)
  have h21 : Entails.eval a c6 := h 5 (by decide)
  have h22 : Entails.eval a c993 := derived993 a h
  have h23 : Entails.eval a c172 := h 171 (by decide)
  have h24 : Entails.eval a c381 := h 380 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c75, some c347, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c95, c75, c347] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c30, some c996, some c972, some c85, some c45, some c312, some c70, some c1002, some c1001, some c93, some c73, some c341, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c22, c30, c996, c972, c85, c45, c312, c70, c1002, c1001, c93, c73, c341] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c996 := derived996 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c1002 := derived1002 a h
  have h9 : Entails.eval a c1001 := derived1001 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c1003, some c119, some c30, some c921, some c368, some c341, some c367, some c97, some c86, some c26, some c359, some c919, some c394, some c38, some c377, some c123, some c390, some c96, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c898, c1003, c119, c30, c921, c368, c341, c367, c97, c86, c26, c359, c919, c394, c38, c377, c123, c390, c96] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c919 := derived919 a h
  have h13 : Entails.eval a c394 := h 393 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c390 := h 389 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c1003, some c119, some c44, some c22, some c30, some c996, some c972, some c921, some c46, some c77, some c301, some c332, some c906, some c133, some c4, some c160, some c140, some c247, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c898, c1003, c119, c44, c22, c30, c996, c972, c921, c46, c77, c301, c332, c906, c133, c4, c160, c140, c247] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c996 := derived996 a h
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c921 := derived921 a h
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c906 := derived906 a h
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨42, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c22, some c996, some c972, some c153, some c133, some c328, some c906, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c1003, c22, c996, c972, c153, c133, c328, c906] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c996 := derived996 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c906 := derived906 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1007 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1005, some c898, some c1003, some c119, some c44, some c22, some c30, some c921, some c86, some c26, some c395, some c379, some c307, some c1006, some c4, some c140, some c239, some c278, some c160, some c359, some c328, some c237, some c222, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1007 : lratChecker f1007 p1007 = .success := by decide +kernel
theorem unsat1007 : Unsatisfiable (PosFin 57) f1007 := by
  apply lratCheckerSound f1007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1007
  · intro a ha; simp [p1007] at ha; subst a; trivial
  · exact checked1007
theorem derived1007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1007 := by
  apply localUnsat_implies_entails f1007 [c1005, c898, c1003, c119, c44, c22, c30, c921, c86, c26, c395, c379, c307, c1006, c4, c140, c239, c278, c160, c359, c328, c237, c222] c1007 unsat1007 (by rfl) a
  have h0 : Entails.eval a c1005 := derived1005 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c395 := h 394 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  have h13 : Entails.eval a c1006 := derived1006 a h
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c278 := h 277 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c359 := h 358 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1008 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨44, by decide⟩, true), (⟨34, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨33, by decide⟩, true), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c239, some c278, some c160, some c250, some c328, some c237, some c286, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1008 : lratChecker f1008 p1008 = .success := by decide +kernel
theorem unsat1008 : Unsatisfiable (PosFin 57) f1008 := by
  apply lratCheckerSound f1008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1008
  · intro a ha; simp [p1008] at ha; subst a; trivial
  · exact checked1008
theorem derived1008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1008 := by
  apply localUnsat_implies_entails f1008 [c140, c239, c278, c160, c250, c328, c237, c286] c1008 unsat1008 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1009 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1005, some c898, some c1003, some c119, some c44, some c22, some c30, some c996, some c972, some c921, some c1007, some c387, some c301, some c379, some c18, some c57, some c323, some c1008, some c4, some c153, some c133, some c328, some c327, some c278, some c276, some c230, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1009 : lratChecker f1009 p1009 = .success := by decide +kernel
theorem unsat1009 : Unsatisfiable (PosFin 57) f1009 := by
  apply lratCheckerSound f1009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1009
  · intro a ha; simp [p1009] at ha; subst a; trivial
  · exact checked1009
theorem derived1009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1009 := by
  apply localUnsat_implies_entails f1009 [c1005, c898, c1003, c119, c44, c22, c30, c996, c972, c921, c1007, c387, c301, c379, c18, c57, c323, c1008, c4, c153, c133, c328, c327, c278, c276, c230] c1009 unsat1009 (by rfl) a
  have h0 : Entails.eval a c1005 := derived1005 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c996 := derived996 a h
  have h8 : Entails.eval a c972 := derived972 a h
  have h9 : Entails.eval a c921 := derived921 a h
  have h10 : Entails.eval a c1007 := derived1007 a h
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  have h17 : Entails.eval a c1008 := derived1008 a h
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c328 := h 327 (by decide)
  have h22 : Entails.eval a c327 := h 326 (by decide)
  have h23 : Entails.eval a c278 := h 277 (by decide)
  have h24 : Entails.eval a c276 := h 275 (by decide)
  have h25 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1010 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c30, some c1005, some c1009, some c70, some c1004, some c368, some c341, some c367, some c86, some c26, some c359, some c48, some c265, some c307, some c28, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1010 : lratChecker f1010 p1010 = .success := by decide +kernel
theorem unsat1010 : Unsatisfiable (PosFin 57) f1010 := by
  apply lratCheckerSound f1010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1010
  · intro a ha; simp [p1010] at ha; subst a; trivial
  · exact checked1010
theorem derived1010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1010 := by
  apply localUnsat_implies_entails f1010 [c22, c30, c1005, c1009, c70, c1004, c368, c341, c367, c86, c26, c359, c48, c265, c307, c28] c1010 unsat1010 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c1005 := derived1005 a h
  have h3 : Entails.eval a c1009 := derived1009 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c1004 := derived1004 a h
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1011 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c48, some c307, some c319, some c100, some c357, some c345, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1011 : lratChecker f1011 p1011 = .success := by decide +kernel
theorem unsat1011 : Unsatisfiable (PosFin 57) f1011 := by
  apply lratCheckerSound f1011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1011
  · intro a ha; simp [p1011] at ha; subst a; trivial
  · exact checked1011
theorem derived1011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1011 := by
  apply localUnsat_implies_entails f1011 [c80, c48, c307, c319, c100, c357, c345] c1011 unsat1011 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1012 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1011, some c367, some c237, some c70, some c20, some c323, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1012 : lratChecker f1012 p1012 = .success := by decide +kernel
theorem unsat1012 : Unsatisfiable (PosFin 57) f1012 := by
  apply lratCheckerSound f1012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1012
  · intro a ha; simp [p1012] at ha; subst a; trivial
  · exact checked1012
theorem derived1012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1012 := by
  apply localUnsat_implies_entails f1012 [c1011, c367, c237, c70, c20, c323] c1012 unsat1012 (by rfl) a
  have h0 : Entails.eval a c1011 := derived1011 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1013 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨42, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c898, some c1003, some c119, some c44, some c921, some c1006, some c4, some c140, some c278, some c248, some c1010, some c22, some c30, some c239, some c160, some c328, some c989, some c38, some c249, some c221, some c120, some c1012, some c379, some c68, some c307, some c237, some c20, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1013 : lratChecker f1013 p1013 = .success := by decide +kernel
theorem unsat1013 : Unsatisfiable (PosFin 57) f1013 := by
  apply lratCheckerSound f1013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1013
  · intro a ha; simp [p1013] at ha; subst a; trivial
  · exact checked1013
theorem derived1013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1013 := by
  apply localUnsat_implies_entails f1013 [c972, c898, c1003, c119, c44, c921, c1006, c4, c140, c278, c248, c1010, c22, c30, c239, c160, c328, c989, c38, c249, c221, c120, c1012, c379, c68, c307, c237, c20] c1013 unsat1013 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c921 := derived921 a h
  have h6 : Entails.eval a c1006 := derived1006 a h
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c1010 := derived1010 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c239 := h 238 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  have h17 : Entails.eval a c989 := derived989 a h
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c1012 := derived1012 a h
  have h23 : Entails.eval a c379 := h 378 (by decide)
  have h24 : Entails.eval a c68 := h 67 (by decide)
  have h25 : Entails.eval a c307 := h 306 (by decide)
  have h26 : Entails.eval a c237 := h 236 (by decide)
  have h27 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1014 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨34, by decide⟩, true), (⟨30, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c332, some c284, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1014 : lratChecker f1014 p1014 = .success := by decide +kernel
theorem unsat1014 : Unsatisfiable (PosFin 57) f1014 := by
  apply lratCheckerSound f1014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1014
  · intro a ha; simp [p1014] at ha; subst a; trivial
  · exact checked1014
theorem derived1014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1014 := by
  apply localUnsat_implies_entails f1014 [c328, c332, c284] c1014 unsat1014 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1015 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨31, by decide⟩, false), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, true), (⟨48, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c307, some c347, some c353, some c286, some c313, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1015 : lratChecker f1015 p1015 = .success := by decide +kernel
theorem unsat1015 : Unsatisfiable (PosFin 57) f1015 := by
  apply lratCheckerSound f1015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1015
  · intro a ha; simp [p1015] at ha; subst a; trivial
  · exact checked1015
theorem derived1015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1015 := by
  apply localUnsat_implies_entails f1015 [c379, c307, c347, c353, c286, c313] c1015 unsat1015 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c286 := h 285 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1016 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨52, by decide⟩, false), (⟨39, by decide⟩, true), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨34, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c781, some c327, some c351, some c170, some c201, some c212, some c176, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1016 : lratChecker f1016 p1016 = .success := by decide +kernel
theorem unsat1016 : Unsatisfiable (PosFin 57) f1016 := by
  apply lratCheckerSound f1016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1016
  · intro a ha; simp [p1016] at ha; subst a; trivial
  · exact checked1016
theorem derived1016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1016 := by
  apply localUnsat_implies_entails f1016 [c51, c781, c327, c351, c170, c201, c212, c176] c1016 unsat1016 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c781 := derived781 a h
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1017 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c1003, some c119, some c44, some c22, some c30, some c996, some c972, some c921, some c1006, some c4, some c140, some c278, some c248, some c1013, some c1014, some c160, some c997, some c247, some c84, some c51, some c71, some c1015, some c1016, some c284, some c989, some c331, some c600, some c222, some c965, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1017 : lratChecker f1017 p1017 = .success := by decide +kernel
theorem unsat1017 : Unsatisfiable (PosFin 57) f1017 := by
  apply lratCheckerSound f1017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1017
  · intro a ha; simp [p1017] at ha; subst a; trivial
  · exact checked1017
theorem derived1017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1017 := by
  apply localUnsat_implies_entails f1017 [c898, c1003, c119, c44, c22, c30, c996, c972, c921, c1006, c4, c140, c278, c248, c1013, c1014, c160, c997, c247, c84, c51, c71, c1015, c1016, c284, c989, c331, c600, c222, c965] c1017 unsat1017 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c996 := derived996 a h
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c921 := derived921 a h
  have h9 : Entails.eval a c1006 := derived1006 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c1013 := derived1013 a h
  have h15 : Entails.eval a c1014 := derived1014 a h
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c997 := derived997 a h
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c84 := h 83 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c71 := h 70 (by decide)
  have h22 : Entails.eval a c1015 := derived1015 a h
  have h23 : Entails.eval a c1016 := derived1016 a h
  have h24 : Entails.eval a c284 := h 283 (by decide)
  have h25 : Entails.eval a c989 := derived989 a h
  have h26 : Entails.eval a c331 := h 330 (by decide)
  have h27 : Entails.eval a c600 := derived600 a h
  have h28 : Entails.eval a c222 := h 221 (by decide)
  have h29 : Entails.eval a c965 := derived965 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1018 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨23, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true), (⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c387, some c153, some c284, some c4, some c341, some c140, some c70, some c278, some c323, some c220, some c1008, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1018 : lratChecker f1018 p1018 = .success := by decide +kernel
theorem unsat1018 : Unsatisfiable (PosFin 57) f1018 := by
  apply lratCheckerSound f1018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1018
  · intro a ha; simp [p1018] at ha; subst a; trivial
  · exact checked1018
theorem derived1018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1018 := by
  apply localUnsat_implies_entails f1018 [c301, c387, c153, c284, c4, c341, c140, c70, c278, c323, c220, c1008] c1018 unsat1018 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c1008 := derived1008 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1019 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨23, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c160, some c247, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1019 : lratChecker f1019 p1019 = .success := by decide +kernel
theorem unsat1019 : Unsatisfiable (PosFin 57) f1019 := by
  apply lratCheckerSound f1019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1019
  · intro a ha; simp [p1019] at ha; subst a; trivial
  · exact checked1019
theorem derived1019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1019 := by
  apply localUnsat_implies_entails f1019 [c140, c160, c247] c1019 unsat1019 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1020 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c898, some c921, some c972, some c996, some c30, some c1003, some c119, some c44, some c1017, some c387, some c379, some c1018, some c328, some c301, some c1010, some c70, some c84, some c395, some c312, some c351, some c745, some c1019, some c8, some c4, some c126, some c133, some c186, some c278, some c208, some c204, some c256, some c146, some c279, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1020 : lratChecker f1020 p1020 = .success := by decide +kernel
theorem unsat1020 : Unsatisfiable (PosFin 57) f1020 := by
  apply lratCheckerSound f1020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1020
  · intro a ha; simp [p1020] at ha; subst a; trivial
  · exact checked1020
theorem derived1020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1020 := by
  apply localUnsat_implies_entails f1020 [c22, c898, c921, c972, c996, c30, c1003, c119, c44, c1017, c387, c379, c1018, c328, c301, c1010, c70, c84, c395, c312, c351, c745, c1019, c8, c4, c126, c133, c186, c278, c208, c204, c256, c146, c279] c1020 unsat1020 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c996 := derived996 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c1017 := derived1017 a h
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c1018 := derived1018 a h
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c1010 := derived1010 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c395 := h 394 (by decide)
  have h19 : Entails.eval a c312 := h 311 (by decide)
  have h20 : Entails.eval a c351 := h 350 (by decide)
  have h21 : Entails.eval a c745 := derived745 a h
  have h22 : Entails.eval a c1019 := derived1019 a h
  have h23 : Entails.eval a c8 := h 7 (by decide)
  have h24 : Entails.eval a c4 := h 3 (by decide)
  have h25 : Entails.eval a c126 := h 125 (by decide)
  have h26 : Entails.eval a c133 := h 132 (by decide)
  have h27 : Entails.eval a c186 := h 185 (by decide)
  have h28 : Entails.eval a c278 := h 277 (by decide)
  have h29 : Entails.eval a c208 := h 207 (by decide)
  have h30 : Entails.eval a c204 := h 203 (by decide)
  have h31 : Entails.eval a c256 := h 255 (by decide)
  have h32 : Entails.eval a c146 := h 145 (by decide)
  have h33 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1021 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c996, some c972, some c921, some c898, some c30, some c22, some c1003, some c119, some c44, some c1010, some c1017, some c387, some c301, some c379, some c1018, some c328, some c1020, some c341, some c154, some c8, some c140, some c192, some c1019, some c278, some c1016, some c133, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1021 : lratChecker f1021 p1021 = .success := by decide +kernel
theorem unsat1021 : Unsatisfiable (PosFin 57) f1021 := by
  apply lratCheckerSound f1021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1021
  · intro a ha; simp [p1021] at ha; subst a; trivial
  · exact checked1021
theorem derived1021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1021 := by
  apply localUnsat_implies_entails f1021 [c996, c972, c921, c898, c30, c22, c1003, c119, c44, c1010, c1017, c387, c301, c379, c1018, c328, c1020, c341, c154, c8, c140, c192, c1019, c278, c1016, c133] c1021 unsat1021 (by rfl) a
  have h0 : Entails.eval a c996 := derived996 a h
  have h1 : Entails.eval a c972 := derived972 a h
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c898 := derived898 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c1010 := derived1010 a h
  have h10 : Entails.eval a c1017 := derived1017 a h
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c1018 := derived1018 a h
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c1020 := derived1020 a h
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c154 := h 153 (by decide)
  have h19 : Entails.eval a c8 := h 7 (by decide)
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c192 := h 191 (by decide)
  have h22 : Entails.eval a c1019 := derived1019 a h
  have h23 : Entails.eval a c278 := h 277 (by decide)
  have h24 : Entails.eval a c1016 := derived1016 a h
  have h25 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1022 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c898, some c1021, some c118, some c85, some c122, some c93, some c979, some c996, some c138, some c977, some c387, some c57, some c95, some c327, some c313, some c56, some c123, some c74, some c94, some c942, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1022 : lratChecker f1022 p1022 = .success := by decide +kernel
theorem unsat1022 : Unsatisfiable (PosFin 57) f1022 := by
  apply lratCheckerSound f1022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1022
  · intro a ha; simp [p1022] at ha; subst a; trivial
  · exact checked1022
theorem derived1022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1022 := by
  apply localUnsat_implies_entails f1022 [c972, c898, c1021, c118, c85, c122, c93, c979, c996, c138, c977, c387, c57, c95, c327, c313, c56, c123, c74, c94, c942] c1022 unsat1022 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1021 := derived1021 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c979 := derived979 a h
  have h8 : Entails.eval a c996 := derived996 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c977 := derived977 a h
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c942 := derived942 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1023 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c898, some c1021, some c118, some c85, some c996, some c122, some c73, some c979, some c921, some c781, some c1022, some c15, some c140, some c160, some c1019, some c239, some c37, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1023 : lratChecker f1023 p1023 = .success := by decide +kernel
theorem unsat1023 : Unsatisfiable (PosFin 57) f1023 := by
  apply lratCheckerSound f1023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1023
  · intro a ha; simp [p1023] at ha; subst a; trivial
  · exact checked1023
theorem derived1023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1023 := by
  apply localUnsat_implies_entails f1023 [c972, c898, c1021, c118, c85, c996, c122, c73, c979, c921, c781, c1022, c15, c140, c160, c1019, c239, c37] c1023 unsat1023 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1021 := derived1021 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c996 := derived996 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c979 := derived979 a h
  have h9 : Entails.eval a c921 := derived921 a h
  have h10 : Entails.eval a c781 := derived781 a h
  have h11 : Entails.eval a c1022 := derived1022 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c1019 := derived1019 a h
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1024 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨30, by decide⟩, false), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c1021, some c122, some c118, some c937, some c996, some c73, some c972, some c93, some c921, some c140, some c160, some c239, some c18, some c331, some c977, some c168, some c978, some c13, some c340, some c75, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1024 : lratChecker f1024 p1024 = .success := by decide +kernel
theorem unsat1024 : Unsatisfiable (PosFin 57) f1024 := by
  apply lratCheckerSound f1024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1024
  · intro a ha; simp [p1024] at ha; subst a; trivial
  · exact checked1024
theorem derived1024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1024 := by
  apply localUnsat_implies_entails f1024 [c898, c1021, c122, c118, c937, c996, c73, c972, c93, c921, c140, c160, c239, c18, c331, c977, c168, c978, c13, c340, c75] c1024 unsat1024 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c1021 := derived1021 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c996 := derived996 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c921 := derived921 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  have h15 : Entails.eval a c977 := derived977 a h
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c978 := derived978 a h
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c340 := h 339 (by decide)
  have h20 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1025 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c898, some c1021, some c118, some c25, some c122, some c93, some c921, some c937, some c1023, some c1024, some c15, some c16, some c138, some c977, some c152, some c387, some c18, some c278, some c276, some c256, some c258, some c230, some c279, some c254, some c226, some c304, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1025 : lratChecker f1025 p1025 = .success := by decide +kernel
theorem unsat1025 : Unsatisfiable (PosFin 57) f1025 := by
  apply lratCheckerSound f1025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1025
  · intro a ha; simp [p1025] at ha; subst a; trivial
  · exact checked1025
theorem derived1025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1025 := by
  apply localUnsat_implies_entails f1025 [c972, c898, c1021, c118, c25, c122, c93, c921, c937, c1023, c1024, c15, c16, c138, c977, c152, c387, c18, c278, c276, c256, c258, c230, c279, c254, c226, c304] c1025 unsat1025 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c1021 := derived1021 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c937 := derived937 a h
  have h9 : Entails.eval a c1023 := derived1023 a h
  have h10 : Entails.eval a c1024 := derived1024 a h
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c977 := derived977 a h
  have h15 : Entails.eval a c152 := h 151 (by decide)
  have h16 : Entails.eval a c387 := h 386 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c256 := h 255 (by decide)
  have h21 : Entails.eval a c258 := h 257 (by decide)
  have h22 : Entails.eval a c230 := h 229 (by decide)
  have h23 : Entails.eval a c279 := h 278 (by decide)
  have h24 : Entails.eval a c254 := h 253 (by decide)
  have h25 : Entails.eval a c226 := h 225 (by decide)
  have h26 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1026 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c921, some c972, some c996, some c1021, some c122, some c118, some c979, some c93, some c73, some c25, some c1025, some c130, some c15, some c978, some c140, some c980, some c386, some c340, some c239, some c94, some c190, some c75, some c18, some c9, some c300, some c156, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1026 : lratChecker f1026 p1026 = .success := by decide +kernel
theorem unsat1026 : Unsatisfiable (PosFin 57) f1026 := by
  apply lratCheckerSound f1026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1026
  · intro a ha; simp [p1026] at ha; subst a; trivial
  · exact checked1026
theorem derived1026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1026 := by
  apply localUnsat_implies_entails f1026 [c898, c921, c972, c996, c1021, c122, c118, c979, c93, c73, c25, c1025, c130, c15, c978, c140, c980, c386, c340, c239, c94, c190, c75, c18, c9, c300, c156] c1026 unsat1026 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c921 := derived921 a h
  have h2 : Entails.eval a c972 := derived972 a h
  have h3 : Entails.eval a c996 := derived996 a h
  have h4 : Entails.eval a c1021 := derived1021 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c979 := derived979 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c1025 := derived1025 a h
  have h12 : Entails.eval a c130 := h 129 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c978 := derived978 a h
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c980 := derived980 a h
  have h17 : Entails.eval a c386 := h 385 (by decide)
  have h18 : Entails.eval a c340 := h 339 (by decide)
  have h19 : Entails.eval a c239 := h 238 (by decide)
  have h20 : Entails.eval a c94 := h 93 (by decide)
  have h21 : Entails.eval a c190 := h 189 (by decide)
  have h22 : Entails.eval a c75 := h 74 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  have h24 : Entails.eval a c9 := h 8 (by decide)
  have h25 : Entails.eval a c300 := h 299 (by decide)
  have h26 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1027 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c18, some c263, some c65, some c105, some c903, some c318, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1027 : lratChecker f1027 p1027 = .success := by decide +kernel
theorem unsat1027 : Unsatisfiable (PosFin 57) f1027 := by
  apply lratCheckerSound f1027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1027
  · intro a ha; simp [p1027] at ha; subst a; trivial
  · exact checked1027
theorem derived1027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1027 := by
  apply localUnsat_implies_entails f1027 [c33, c18, c263, c65, c105, c903, c318] c1027 unsat1027 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c903 := derived903 a h
  have h6 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1028 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1027, some c267, some c66, some c105, some c239, some c263, some c160, some c17, some c314, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1028 : lratChecker f1028 p1028 = .success := by decide +kernel
theorem unsat1028 : Unsatisfiable (PosFin 57) f1028 := by
  apply lratCheckerSound f1028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1028
  · intro a ha; simp [p1028] at ha; subst a; trivial
  · exact checked1028
theorem derived1028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1028 := by
  apply localUnsat_implies_entails f1028 [c1027, c267, c66, c105, c239, c263, c160, c17, c314] c1028 unsat1028 (by rfl) a
  have h0 : Entails.eval a c1027 := derived1027 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1029 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c17, some c298, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1029 : lratChecker f1029 p1029 = .success := by decide +kernel
theorem unsat1029 : Unsatisfiable (PosFin 57) f1029 := by
  apply lratCheckerSound f1029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1029
  · intro a ha; simp [p1029] at ha; subst a; trivial
  · exact checked1029
theorem derived1029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1029 := by
  apply localUnsat_implies_entails f1029 [c25, c17, c298] c1029 unsat1029 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1030 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c298, some c85, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1030 : lratChecker f1030 p1030 = .success := by decide +kernel
theorem unsat1030 : Unsatisfiable (PosFin 57) f1030 := by
  apply lratCheckerSound f1030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1030
  · intro a ha; simp [p1030] at ha; subst a; trivial
  · exact checked1030
theorem derived1030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1030 := by
  apply localUnsat_implies_entails f1030 [c314, c298, c85] c1030 unsat1030 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1031 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, true), (⟨56, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1028, some c140, some c132, some c1030, some c53, some c302, some c318, some c86, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1031 : lratChecker f1031 p1031 = .success := by decide +kernel
theorem unsat1031 : Unsatisfiable (PosFin 57) f1031 := by
  apply lratCheckerSound f1031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1031
  · intro a ha; simp [p1031] at ha; subst a; trivial
  · exact checked1031
theorem derived1031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1031 := by
  apply localUnsat_implies_entails f1031 [c1028, c140, c132, c1030, c53, c302, c318, c86] c1031 unsat1031 (by rfl) a
  have h0 : Entails.eval a c1028 := derived1028 a h
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c1030 := derived1030 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1032 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c118, some c1026, some c122, some c1031, some c15, some c138, some c130, some c659, some c45, some c53, some c17, some c301, some c93, some c86, some c336, some c396, some c362, some c337, some c234, some c139, some c31, some c16, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1032 : lratChecker f1032 p1032 = .success := by decide +kernel
theorem unsat1032 : Unsatisfiable (PosFin 57) f1032 := by
  apply lratCheckerSound f1032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1032
  · intro a ha; simp [p1032] at ha; subst a; trivial
  · exact checked1032
theorem derived1032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1032 := by
  apply localUnsat_implies_entails f1032 [c898, c118, c1026, c122, c1031, c15, c138, c130, c659, c45, c53, c17, c301, c93, c86, c336, c396, c362, c337, c234, c139, c31, c16] c1032 unsat1032 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c1026 := derived1026 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c1031 := derived1031 a h
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c659 := derived659 a h
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c396 := h 395 (by decide)
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c337 := h 336 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c139 := h 138 (by decide)
  have h21 : Entails.eval a c31 := h 30 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1033 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1026, some c898, some c118, some c122, some c1031, some c15, some c130, some c138, some c1032, some c296, some c85, some c392, some c659, some c93, some c977, some c46, some c341, some c362, some c387, some c199, some c186, some c95, some c18, some c907, some c256, some c279, some c254, some c146, some c339, some c9, some c218, some c74, some c181, some c363, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1033 : lratChecker f1033 p1033 = .success := by decide +kernel
theorem unsat1033 : Unsatisfiable (PosFin 57) f1033 := by
  apply lratCheckerSound f1033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1033
  · intro a ha; simp [p1033] at ha; subst a; trivial
  · exact checked1033
theorem derived1033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1033 := by
  apply localUnsat_implies_entails f1033 [c1026, c898, c118, c122, c1031, c15, c130, c138, c1032, c296, c85, c392, c659, c93, c977, c46, c341, c362, c387, c199, c186, c95, c18, c907, c256, c279, c254, c146, c339, c9, c218, c74, c181, c363] c1033 unsat1033 (by rfl) a
  have h0 : Entails.eval a c1026 := derived1026 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c1031 := derived1031 a h
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c1032 := derived1032 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c392 := h 391 (by decide)
  have h12 : Entails.eval a c659 := derived659 a h
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c977 := derived977 a h
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c341 := h 340 (by decide)
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c387 := h 386 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c186 := h 185 (by decide)
  have h21 : Entails.eval a c95 := h 94 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c907 := derived907 a h
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c279 := h 278 (by decide)
  have h26 : Entails.eval a c254 := h 253 (by decide)
  have h27 : Entails.eval a c146 := h 145 (by decide)
  have h28 : Entails.eval a c339 := h 338 (by decide)
  have h29 : Entails.eval a c9 := h 8 (by decide)
  have h30 : Entails.eval a c218 := h 217 (by decide)
  have h31 : Entails.eval a c74 := h 73 (by decide)
  have h32 : Entails.eval a c181 := h 180 (by decide)
  have h33 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1034 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1026, some c898, some c122, some c118, some c1031, some c15, some c130, some c138, some c1032, some c296, some c1033, some c890, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1034 : lratChecker f1034 p1034 = .success := by decide +kernel
theorem unsat1034 : Unsatisfiable (PosFin 57) f1034 := by
  apply lratCheckerSound f1034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1034
  · intro a ha; simp [p1034] at ha; subst a; trivial
  · exact checked1034
theorem derived1034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1034 := by
  apply localUnsat_implies_entails f1034 [c1026, c898, c122, c118, c1031, c15, c130, c138, c1032, c296, c1033, c890] c1034 unsat1034 (by rfl) a
  have h0 : Entails.eval a c1026 := derived1026 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c1031 := derived1031 a h
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c1032 := derived1032 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c1033 := derived1033 a h
  have h11 : Entails.eval a c890 := derived890 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1035 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1034, some c22, some c30, some c1026, some c898, some c890, some c296, some c45, some c17, some c336, some c278, some c70, some c44, some c325, some c903, some c210, some c16, some c152, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1035 : lratChecker f1035 p1035 = .success := by decide +kernel
theorem unsat1035 : Unsatisfiable (PosFin 57) f1035 := by
  apply lratCheckerSound f1035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1035
  · intro a ha; simp [p1035] at ha; subst a; trivial
  · exact checked1035
theorem derived1035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1035 := by
  apply localUnsat_implies_entails f1035 [c1034, c22, c30, c1026, c898, c890, c296, c45, c17, c336, c278, c70, c44, c325, c903, c210, c16, c152] c1035 unsat1035 (by rfl) a
  have h0 : Entails.eval a c1034 := derived1034 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1026 := derived1026 a h
  have h4 : Entails.eval a c898 := derived898 a h
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c278 := h 277 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c325 := h 324 (by decide)
  have h14 : Entails.eval a c903 := derived903 a h
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1036 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c45, some c1035, some c907, some c140, some c1034, some c898, some c982, some c16, some c152, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1036 : lratChecker f1036 p1036 = .success := by decide +kernel
theorem unsat1036 : Unsatisfiable (PosFin 57) f1036 := by
  apply lratCheckerSound f1036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1036
  · intro a ha; simp [p1036] at ha; subst a; trivial
  · exact checked1036
theorem derived1036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1036 := by
  apply localUnsat_implies_entails f1036 [c17, c45, c1035, c907, c140, c1034, c898, c982, c16, c152] c1036 unsat1036 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c907 := derived907 a h
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c1034 := derived1034 a h
  have h6 : Entails.eval a c898 := derived898 a h
  have h7 : Entails.eval a c982 := derived982 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1037 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1034, some c1026, some c659, some c44, some c71, some c234, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1037 : lratChecker f1037 p1037 = .success := by decide +kernel
theorem unsat1037 : Unsatisfiable (PosFin 57) f1037 := by
  apply lratCheckerSound f1037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1037
  · intro a ha; simp [p1037] at ha; subst a; trivial
  · exact checked1037
theorem derived1037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1037 := by
  apply localUnsat_implies_entails f1037 [c1034, c1026, c659, c44, c71, c234] c1037 unsat1037 (by rfl) a
  have h0 : Entails.eval a c1034 := derived1034 a h
  have h1 : Entails.eval a c1026 := derived1026 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1038 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1035, some c907, some c140, some c1034, some c22, some c30, some c1026, some c898, some c45, some c17, some c1037, some c1036, some c325, some c332, some c937, some c70, some c8, some c336, some c161, some c85, some c199, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1038 : lratChecker f1038 p1038 = .success := by decide +kernel
theorem unsat1038 : Unsatisfiable (PosFin 57) f1038 := by
  apply lratCheckerSound f1038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1038
  · intro a ha; simp [p1038] at ha; subst a; trivial
  · exact checked1038
theorem derived1038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1038 := by
  apply localUnsat_implies_entails f1038 [c1035, c907, c140, c1034, c22, c30, c1026, c898, c45, c17, c1037, c1036, c325, c332, c937, c70, c8, c336, c161, c85, c199] c1038 unsat1038 (by rfl) a
  have h0 : Entails.eval a c1035 := derived1035 a h
  have h1 : Entails.eval a c907 := derived907 a h
  have h2 : Entails.eval a c140 := h 139 (by decide)
  have h3 : Entails.eval a c1034 := derived1034 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c1026 := derived1026 a h
  have h7 : Entails.eval a c898 := derived898 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c1037 := derived1037 a h
  have h11 : Entails.eval a c1036 := derived1036 a h
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c332 := h 331 (by decide)
  have h14 : Entails.eval a c937 := derived937 a h
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c85 := h 84 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1039 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1035, some c1034, some c22, some c30, some c1026, some c659, some c898, some c907, some c140, some c1038, some c296, some c328, some c85, some c25, some c983, some c392, some c116, some c16, some c152, some c276, some c902, some c42, some c124, some c74, some c38, some c242, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1039 : lratChecker f1039 p1039 = .success := by decide +kernel
theorem unsat1039 : Unsatisfiable (PosFin 57) f1039 := by
  apply lratCheckerSound f1039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1039
  · intro a ha; simp [p1039] at ha; subst a; trivial
  · exact checked1039
theorem derived1039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1039 := by
  apply localUnsat_implies_entails f1039 [c1035, c1034, c22, c30, c1026, c659, c898, c907, c140, c1038, c296, c328, c85, c25, c983, c392, c116, c16, c152, c276, c902, c42, c124, c74, c38, c242] c1039 unsat1039 (by rfl) a
  have h0 : Entails.eval a c1035 := derived1035 a h
  have h1 : Entails.eval a c1034 := derived1034 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c1026 := derived1026 a h
  have h5 : Entails.eval a c659 := derived659 a h
  have h6 : Entails.eval a c898 := derived898 a h
  have h7 : Entails.eval a c907 := derived907 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c1038 := derived1038 a h
  have h10 : Entails.eval a c296 := h 295 (by decide)
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c983 := derived983 a h
  have h15 : Entails.eval a c392 := h 391 (by decide)
  have h16 : Entails.eval a c116 := h 115 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c152 := h 151 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c902 := derived902 a h
  have h21 : Entails.eval a c42 := h 41 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c74 := h 73 (by decide)
  have h24 : Entails.eval a c38 := h 37 (by decide)
  have h25 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1040 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1039, some c1035, some c1034, some c22, some c30, some c1026, some c296, some c328, some c85, some c132, some c392, some c199, some c217, some c983, some c70, some c172, some c184, some c341, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1040 : lratChecker f1040 p1040 = .success := by decide +kernel
theorem unsat1040 : Unsatisfiable (PosFin 57) f1040 := by
  apply lratCheckerSound f1040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1040
  · intro a ha; simp [p1040] at ha; subst a; trivial
  · exact checked1040
theorem derived1040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1040 := by
  apply localUnsat_implies_entails f1040 [c1039, c1035, c1034, c22, c30, c1026, c296, c328, c85, c132, c392, c199, c217, c983, c70, c172, c184, c341] c1040 unsat1040 (by rfl) a
  have h0 : Entails.eval a c1039 := derived1039 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c1034 := derived1034 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1026 := derived1026 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c392 := h 391 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c983 := derived983 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1041 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1040, some c17, some c45, some c1037, some c1039, some c1035, some c1034, some c30, some c1026, some c898, some c132, some c982, some c210, some c16, some c70, some c984, some c336, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1041 : lratChecker f1041 p1041 = .success := by decide +kernel
theorem unsat1041 : Unsatisfiable (PosFin 57) f1041 := by
  apply lratCheckerSound f1041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1041
  · intro a ha; simp [p1041] at ha; subst a; trivial
  · exact checked1041
theorem derived1041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1041 := by
  apply localUnsat_implies_entails f1041 [c1040, c17, c45, c1037, c1039, c1035, c1034, c30, c1026, c898, c132, c982, c210, c16, c70, c984, c336] c1041 unsat1041 (by rfl) a
  have h0 : Entails.eval a c1040 := derived1040 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1039 := derived1039 a h
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c1034 := derived1034 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c1026 := derived1026 a h
  have h9 : Entails.eval a c898 := derived898 a h
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c982 := derived982 a h
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c984 := derived984 a h
  have h16 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1042 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1034, some c22, some c898, some c1035, some c1039, some c1040, some c1041, some c916, some c332, some c937, some c140, some c8, some c213, some c161, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1042 : lratChecker f1042 p1042 = .success := by decide +kernel
theorem unsat1042 : Unsatisfiable (PosFin 57) f1042 := by
  apply lratCheckerSound f1042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1042
  · intro a ha; simp [p1042] at ha; subst a; trivial
  · exact checked1042
theorem derived1042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1042 := by
  apply localUnsat_implies_entails f1042 [c1034, c22, c898, c1035, c1039, c1040, c1041, c916, c332, c937, c140, c8, c213, c161] c1042 unsat1042 (by rfl) a
  have h0 : Entails.eval a c1034 := derived1034 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c898 := derived898 a h
  have h3 : Entails.eval a c1035 := derived1035 a h
  have h4 : Entails.eval a c1039 := derived1039 a h
  have h5 : Entails.eval a c1040 := derived1040 a h
  have h6 : Entails.eval a c1041 := derived1041 a h
  have h7 : Entails.eval a c916 := derived916 a h
  have h8 : Entails.eval a c332 := h 331 (by decide)
  have h9 : Entails.eval a c937 := derived937 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1043 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c1026, some c659, some c1034, some c30, some c22, some c1042, some c119, some c44, some c116, some c71, some c91, some c392, some c396, some c325, some c507, some c109, some c1019, some c8, some c4, some c210, some c940, some c296, some c184, some c133, some c977, some c387, some c278, some c276, some c126, some c256, some c258, some c279, some c390, some c254, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1043 : lratChecker f1043 p1043 = .success := by decide +kernel
theorem unsat1043 : Unsatisfiable (PosFin 57) f1043 := by
  apply lratCheckerSound f1043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1043
  · intro a ha; simp [p1043] at ha; subst a; trivial
  · exact checked1043
theorem derived1043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1043 := by
  apply localUnsat_implies_entails f1043 [c898, c1026, c659, c1034, c30, c22, c1042, c119, c44, c116, c71, c91, c392, c396, c325, c507, c109, c1019, c8, c4, c210, c940, c296, c184, c133, c977, c387, c278, c276, c126, c256, c258, c279, c390, c254] c1043 unsat1043 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c1026 := derived1026 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c1034 := derived1034 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1042 := derived1042 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c392 := h 391 (by decide)
  have h13 : Entails.eval a c396 := h 395 (by decide)
  have h14 : Entails.eval a c325 := h 324 (by decide)
  have h15 : Entails.eval a c507 := derived507 a h
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c1019 := derived1019 a h
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c4 := h 3 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c940 := derived940 a h
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c184 := h 183 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  have h25 : Entails.eval a c977 := derived977 a h
  have h26 : Entails.eval a c387 := h 386 (by decide)
  have h27 : Entails.eval a c278 := h 277 (by decide)
  have h28 : Entails.eval a c276 := h 275 (by decide)
  have h29 : Entails.eval a c126 := h 125 (by decide)
  have h30 : Entails.eval a c256 := h 255 (by decide)
  have h31 : Entails.eval a c258 := h 257 (by decide)
  have h32 : Entails.eval a c279 := h 278 (by decide)
  have h33 : Entails.eval a c390 := h 389 (by decide)
  have h34 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1044 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c340, some c366, some c371, some c78, some c173, some c383, some c102, some c187, some c10, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1044 : lratChecker f1044 p1044 = .success := by decide +kernel
theorem unsat1044 : Unsatisfiable (PosFin 57) f1044 := by
  apply lratCheckerSound f1044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1044
  · intro a ha; simp [p1044] at ha; subst a; trivial
  · exact checked1044
theorem derived1044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1044 := by
  apply localUnsat_implies_entails f1044 [c353, c340, c366, c371, c78, c173, c383, c102, c187, c10] c1044 unsat1044 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c173 := h 172 (by decide)
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1045 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨48, by decide⟩, true), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c24, some c119, some c126, some c154, some c280, some c238, some c256, some c228, some c70, some c84, some c323, some c307, some c312, some c266, some c104, some c1044, some c973, some c363, some c337, some c293, some c133, some c327, some c234, some c23, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1045 : lratChecker f1045 p1045 = .success := by decide +kernel
theorem unsat1045 : Unsatisfiable (PosFin 57) f1045 := by
  apply lratCheckerSound f1045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1045
  · intro a ha; simp [p1045] at ha; subst a; trivial
  · exact checked1045
theorem derived1045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1045 := by
  apply localUnsat_implies_entails f1045 [c1043, c24, c119, c126, c154, c280, c238, c256, c228, c70, c84, c323, c307, c312, c266, c104, c1044, c973, c363, c337, c293, c133, c327, c234, c23] c1045 unsat1045 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c238 := h 237 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c307 := h 306 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c104 := h 103 (by decide)
  have h16 : Entails.eval a c1044 := derived1044 a h
  have h17 : Entails.eval a c973 := derived973 a h
  have h18 : Entails.eval a c363 := h 362 (by decide)
  have h19 : Entails.eval a c337 := h 336 (by decide)
  have h20 : Entails.eval a c293 := h 292 (by decide)
  have h21 : Entails.eval a c133 := h 132 (by decide)
  have h22 : Entails.eval a c327 := h 326 (by decide)
  have h23 : Entails.eval a c234 := h 233 (by decide)
  have h24 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1046 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c119, some c973, some c233, some c84, some c363, some c234, some c293, some c23, some c327, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1046 : lratChecker f1046 p1046 = .success := by decide +kernel
theorem unsat1046 : Unsatisfiable (PosFin 57) f1046 := by
  apply lratCheckerSound f1046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1046
  · intro a ha; simp [p1046] at ha; subst a; trivial
  · exact checked1046
theorem derived1046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1046 := by
  apply localUnsat_implies_entails f1046 [c1043, c119, c973, c233, c84, c363, c234, c293, c23, c327] c1046 unsat1046 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1047 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c24, some c119, some c1045, some c331, some c228, some c280, some c141, some c134, some c301, some c90, some c272, some c312, some c317, some c1046, some c351, some c353, some c340, some c366, some c367, some c379, some c88, some c78, some c659, some c120, some c109, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1047 : lratChecker f1047 p1047 = .success := by decide +kernel
theorem unsat1047 : Unsatisfiable (PosFin 57) f1047 := by
  apply lratCheckerSound f1047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1047
  · intro a ha; simp [p1047] at ha; subst a; trivial
  · exact checked1047
theorem derived1047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1047 := by
  apply localUnsat_implies_entails f1047 [c1043, c24, c119, c1045, c331, c228, c280, c141, c134, c301, c90, c272, c312, c317, c1046, c351, c353, c340, c366, c367, c379, c88, c78, c659, c120, c109] c1047 unsat1047 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c1045 := derived1045 a h
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c280 := h 279 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c312 := h 311 (by decide)
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c1046 := derived1046 a h
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c353 := h 352 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c366 := h 365 (by decide)
  have h19 : Entails.eval a c367 := h 366 (by decide)
  have h20 : Entails.eval a c379 := h 378 (by decide)
  have h21 : Entails.eval a c88 := h 87 (by decide)
  have h22 : Entails.eval a c78 := h 77 (by decide)
  have h23 : Entails.eval a c659 := derived659 a h
  have h24 : Entails.eval a c120 := h 119 (by decide)
  have h25 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1048 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨34, by decide⟩, false), (⟨48, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c134, some c126, some c388, some c342, some c331, some c104, some c291, some c228, some c385, some c340, some c272, some c373, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1048 : lratChecker f1048 p1048 = .success := by decide +kernel
theorem unsat1048 : Unsatisfiable (PosFin 57) f1048 := by
  apply lratCheckerSound f1048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1048
  · intro a ha; simp [p1048] at ha; subst a; trivial
  · exact checked1048
theorem derived1048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1048 := by
  apply localUnsat_implies_entails f1048 [c1043, c134, c126, c388, c342, c331, c104, c291, c228, c385, c340, c272, c373] c1048 unsat1048 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c340 := h 339 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1049 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨48, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c172, some c70, some c312, some c1048, some c280, some c266, some c228, some c507, some c323, some c104, some c1044, some c385, some c373, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1049 : lratChecker f1049 p1049 = .success := by decide +kernel
theorem unsat1049 : Unsatisfiable (PosFin 57) f1049 := by
  apply lratCheckerSound f1049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1049
  · intro a ha; simp [p1049] at ha; subst a; trivial
  · exact checked1049
theorem derived1049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1049 := by
  apply localUnsat_implies_entails f1049 [c1043, c172, c70, c312, c1048, c280, c266, c228, c507, c323, c104, c1044, c385, c373] c1049 unsat1049 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c1048 := derived1048 a h
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c507 := derived507 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c1044 := derived1044 a h
  have h12 : Entails.eval a c385 := h 384 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1050 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨48, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c172, some c1049, some c238, some c367, some c368, some c126, some c291, some c331, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1050 : lratChecker f1050 p1050 = .success := by decide +kernel
theorem unsat1050 : Unsatisfiable (PosFin 57) f1050 := by
  apply lratCheckerSound f1050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1050
  · intro a ha; simp [p1050] at ha; subst a; trivial
  · exact checked1050
theorem derived1050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1050 := by
  apply localUnsat_implies_entails f1050 [c1043, c172, c1049, c238, c367, c368, c126, c291, c331] c1050 unsat1050 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c238 := h 237 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1051 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c119, some c1047, some c1050, some c1046, some c133, some c384, some c385, some c104, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1051 : lratChecker f1051 p1051 = .success := by decide +kernel
theorem unsat1051 : Unsatisfiable (PosFin 57) f1051 := by
  apply lratCheckerSound f1051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1051
  · intro a ha; simp [p1051] at ha; subst a; trivial
  · exact checked1051
theorem derived1051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1051 := by
  apply localUnsat_implies_entails f1051 [c24, c119, c1047, c1050, c1046, c133, c384, c385, c104] c1051 unsat1051 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c1047 := derived1047 a h
  have h3 : Entails.eval a c1050 := derived1050 a h
  have h4 : Entails.eval a c1046 := derived1046 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1052 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c1046, some c133, some c296, some c104, some c337, some c297, some c51, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1052 : lratChecker f1052 p1052 = .success := by decide +kernel
theorem unsat1052 : Unsatisfiable (PosFin 57) f1052 := by
  apply lratCheckerSound f1052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1052
  · intro a ha; simp [p1052] at ha; subst a; trivial
  · exact checked1052
theorem derived1052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1052 := by
  apply localUnsat_implies_entails f1052 [c119, c1046, c133, c296, c104, c337, c297, c51] c1052 unsat1052 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1053 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c383, some c297, some c258, some c23, some c57, some c283, some c317, some c254, some c226, some c86, some c299, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1053 : lratChecker f1053 p1053 = .success := by decide +kernel
theorem unsat1053 : Unsatisfiable (PosFin 57) f1053 := by
  apply lratCheckerSound f1053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1053
  · intro a ha; simp [p1053] at ha; subst a; trivial
  · exact checked1053
theorem derived1053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1053 := by
  apply localUnsat_implies_entails f1053 [c385, c383, c297, c258, c23, c57, c283, c317, c254, c226, c86, c299] c1053 unsat1053 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c297 := h 296 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1054 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c331, some c317, some c228, some c351, some c86, some c272, some c353, some c373, some c340, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1054 : lratChecker f1054 p1054 = .success := by decide +kernel
theorem unsat1054 : Unsatisfiable (PosFin 57) f1054 := by
  apply lratCheckerSound f1054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1054
  · intro a ha; simp [p1054] at ha; subst a; trivial
  · exact checked1054
theorem derived1054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1054 := by
  apply localUnsat_implies_entails f1054 [c1043, c331, c317, c228, c351, c86, c272, c353, c373, c340] c1054 unsat1054 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c228 := h 227 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1055 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1054, some c46, some c18, some c280, some c266, some c228, some c86, some c323, some c353, some c373, some c340, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1055 : lratChecker f1055 p1055 = .success := by decide +kernel
theorem unsat1055 : Unsatisfiable (PosFin 57) f1055 := by
  apply lratCheckerSound f1055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1055
  · intro a ha; simp [p1055] at ha; subst a; trivial
  · exact checked1055
theorem derived1055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1055 := by
  apply localUnsat_implies_entails f1055 [c1043, c1054, c46, c18, c280, c266, c228, c86, c323, c353, c373, c340] c1055 unsat1055 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1054 := derived1054 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c373 := h 372 (by decide)
  have h11 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1056 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c90, some c104, some c312, some c1053, some c1055, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1056 : lratChecker f1056 p1056 = .success := by decide +kernel
theorem unsat1056 : Unsatisfiable (PosFin 57) f1056 := by
  apply lratCheckerSound f1056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1056
  · intro a ha; simp [p1056] at ha; subst a; trivial
  · exact checked1056
theorem derived1056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1056 := by
  apply localUnsat_implies_entails f1056 [c90, c104, c312, c1053, c1055] c1056 unsat1056 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c1053 := derived1053 a h
  have h4 : Entails.eval a c1055 := derived1055 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1057 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨41, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c312, some c1055, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1057 : lratChecker f1057 p1057 = .success := by decide +kernel
theorem unsat1057 : Unsatisfiable (PosFin 57) f1057 := by
  apply lratCheckerSound f1057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1057
  · intro a ha; simp [p1057] at ha; subst a; trivial
  · exact checked1057
theorem derived1057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1057 := by
  apply localUnsat_implies_entails f1057 [c312, c1055] c1057 unsat1057 (by rfl) a
  have h0 : Entails.eval a c312 := h 311 (by decide)
  have h1 : Entails.eval a c1055 := derived1055 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1058 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨38, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c46, some c18, some c238, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1058 : lratChecker f1058 p1058 = .success := by decide +kernel
theorem unsat1058 : Unsatisfiable (PosFin 57) f1058 := by
  apply lratCheckerSound f1058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1058
  · intro a ha; simp [p1058] at ha; subst a; trivial
  · exact checked1058
theorem derived1058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1058 := by
  apply localUnsat_implies_entails f1058 [c1043, c46, c18, c238] c1058 unsat1058 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1059 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1056, some c296, some c1057, some c70, some c1058, some c331, some c301, some c228, some c26, some c280, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1059 : lratChecker f1059 p1059 = .success := by decide +kernel
theorem unsat1059 : Unsatisfiable (PosFin 57) f1059 := by
  apply lratCheckerSound f1059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1059
  · intro a ha; simp [p1059] at ha; subst a; trivial
  · exact checked1059
theorem derived1059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1059 := by
  apply localUnsat_implies_entails f1059 [c1043, c1056, c296, c1057, c70, c1058, c331, c301, c228, c26, c280] c1059 unsat1059 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1056 := derived1056 a h
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c1057 := derived1057 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1060 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c4, some c119, some c1051, some c8, some c1052, some c1059, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1060 : lratChecker f1060 p1060 = .success := by decide +kernel
theorem unsat1060 : Unsatisfiable (PosFin 57) f1060 := by
  apply lratCheckerSound f1060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1060
  · intro a ha; simp [p1060] at ha; subst a; trivial
  · exact checked1060
theorem derived1060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1060 := by
  apply localUnsat_implies_entails f1060 [c24, c4, c119, c1051, c8, c1052, c1059] c1060 unsat1060 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c1051 := derived1051 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c1052 := derived1052 a h
  have h6 : Entails.eval a c1059 := derived1059 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1061 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c165, some c10, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1061 : lratChecker f1061 p1061 = .success := by decide +kernel
theorem unsat1061 : Unsatisfiable (PosFin 57) f1061 := by
  apply lratCheckerSound f1061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1061
  · intro a ha; simp [p1061] at ha; subst a; trivial
  · exact checked1061
theorem derived1061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1061 := by
  apply localUnsat_implies_entails f1061 [c58, c165, c10] c1061 unsat1061 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1062 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c228, some c244, some c48, some c156, some c12, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1062 : lratChecker f1062 p1062 = .success := by decide +kernel
theorem unsat1062 : Unsatisfiable (PosFin 57) f1062 := by
  apply lratCheckerSound f1062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1062
  · intro a ha; simp [p1062] at ha; subst a; trivial
  · exact checked1062
theorem derived1062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1062 := by
  apply localUnsat_implies_entails f1062 [c1043, c228, c244, c48, c156, c12] c1062 unsat1062 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1063 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c24, some c119, some c1060, some c158, some c64, some c327, some c62, some c169, some c1061, some c1062, some c330, some c1058, some c8, some c126, some c154, some c238, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1063 : lratChecker f1063 p1063 = .success := by decide +kernel
theorem unsat1063 : Unsatisfiable (PosFin 57) f1063 := by
  apply lratCheckerSound f1063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1063
  · intro a ha; simp [p1063] at ha; subst a; trivial
  · exact checked1063
theorem derived1063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1063 := by
  apply localUnsat_implies_entails f1063 [c1043, c24, c119, c1060, c158, c64, c327, c62, c169, c1061, c1062, c330, c1058, c8, c126, c154, c238] c1063 unsat1063 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c1060 := derived1060 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  have h9 : Entails.eval a c1061 := derived1061 a h
  have h10 : Entails.eval a c1062 := derived1062 a h
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c1058 := derived1058 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1064 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1063, some c281, some c277, some c158, some c246, some c52, some c119, some c4, some c64, some c133, some c141, some c327, some c297, some c8, some c62, some c169, some c91, some c97, some c104, some c1058, some c1061, some c659, some c321, some c299, some c388, some c377, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1064 : lratChecker f1064 p1064 = .success := by decide +kernel
theorem unsat1064 : Unsatisfiable (PosFin 57) f1064 := by
  apply lratCheckerSound f1064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1064
  · intro a ha; simp [p1064] at ha; subst a; trivial
  · exact checked1064
theorem derived1064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1064 := by
  apply localUnsat_implies_entails f1064 [c1043, c1063, c281, c277, c158, c246, c52, c119, c4, c64, c133, c141, c327, c297, c8, c62, c169, c91, c97, c104, c1058, c1061, c659, c321, c299, c388, c377] c1064 unsat1064 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1063 := derived1063 a h
  have h2 : Entails.eval a c281 := h 280 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c91 := h 90 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c104 := h 103 (by decide)
  have h20 : Entails.eval a c1058 := derived1058 a h
  have h21 : Entails.eval a c1061 := derived1061 a h
  have h22 : Entails.eval a c659 := derived659 a h
  have h23 : Entails.eval a c321 := h 320 (by decide)
  have h24 : Entails.eval a c299 := h 298 (by decide)
  have h25 : Entails.eval a c388 := h 387 (by decide)
  have h26 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1065 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c331, some c281, some c277, some c133, some c141, some c296, some c90, some c104, some c274, some c297, some c385, some c60, some c92, some c123, some c8, some c98, some c26, some c299, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1065 : lratChecker f1065 p1065 = .success := by decide +kernel
theorem unsat1065 : Unsatisfiable (PosFin 57) f1065 := by
  apply lratCheckerSound f1065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1065
  · intro a ha; simp [p1065] at ha; subst a; trivial
  · exact checked1065
theorem derived1065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1065 := by
  apply localUnsat_implies_entails f1065 [c1043, c331, c281, c277, c133, c141, c296, c90, c104, c274, c297, c385, c60, c92, c123, c8, c98, c26, c299] c1065 unsat1065 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1066 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c331, some c117, some c1065, some c4, some c1, some c52, some c61, some c157, some c246, some c123, some c84, some c78, some c370, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1066 : lratChecker f1066 p1066 = .success := by decide +kernel
theorem unsat1066 : Unsatisfiable (PosFin 57) f1066 := by
  apply lratCheckerSound f1066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1066
  · intro a ha; simp [p1066] at ha; subst a; trivial
  · exact checked1066
theorem derived1066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1066 := by
  apply localUnsat_implies_entails f1066 [c1043, c331, c117, c1065, c4, c1, c52, c61, c157, c246, c123, c84, c78, c370] c1066 unsat1066 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c1065 := derived1065 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1067 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c277, some c1066, some c63, some c119, some c4, some c133, some c296, some c104, some c102, some c383, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1067 : lratChecker f1067 p1067 = .success := by decide +kernel
theorem unsat1067 : Unsatisfiable (PosFin 57) f1067 := by
  apply lratCheckerSound f1067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1067
  · intro a ha; simp [p1067] at ha; subst a; trivial
  · exact checked1067
theorem derived1067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1067 := by
  apply localUnsat_implies_entails f1067 [c1043, c277, c1066, c63, c119, c4, c133, c296, c104, c102, c383] c1067 unsat1067 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c1066 := derived1066 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1068 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c295, some c102, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1068 : lratChecker f1068 p1068 = .success := by decide +kernel
theorem unsat1068 : Unsatisfiable (PosFin 57) f1068 := by
  apply lratCheckerSound f1068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1068
  · intro a ha; simp [p1068] at ha; subst a; trivial
  · exact checked1068
theorem derived1068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1068 := by
  apply localUnsat_implies_entails f1068 [c296, c295, c102] c1068 unsat1068 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1069 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨31, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c214, some c712, some c52, some c131, some c247, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1069 : lratChecker f1069 p1069 = .success := by decide +kernel
theorem unsat1069 : Unsatisfiable (PosFin 57) f1069 := by
  apply lratCheckerSound f1069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1069
  · intro a ha; simp [p1069] at ha; subst a; trivial
  · exact checked1069
theorem derived1069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1069 := by
  apply localUnsat_implies_entails f1069 [c4, c214, c712, c52, c131, c247] c1069 unsat1069 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1070 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c277, some c1067, some c327, some c1069, some c133, some c1068, some c117, some c1065, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1070 : lratChecker f1070 p1070 = .success := by decide +kernel
theorem unsat1070 : Unsatisfiable (PosFin 57) f1070 := by
  apply lratCheckerSound f1070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1070
  · intro a ha; simp [p1070] at ha; subst a; trivial
  · exact checked1070
theorem derived1070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1070 := by
  apply localUnsat_implies_entails f1070 [c1043, c277, c1067, c327, c1069, c133, c1068, c117, c1065] c1070 unsat1070 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c1067 := derived1067 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c1069 := derived1069 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c1068 := derived1068 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c1065 := derived1065 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1071 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨41, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c90, some c312, some c327, some c1068, some c117, some c23, some c51, some c104, some c337, some c247, some c351, some c291, some c289, some c366, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1071 : lratChecker f1071 p1071 = .success := by decide +kernel
theorem unsat1071 : Unsatisfiable (PosFin 57) f1071 := by
  apply lratCheckerSound f1071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1071
  · intro a ha; simp [p1071] at ha; subst a; trivial
  · exact checked1071
theorem derived1071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1071 := by
  apply localUnsat_implies_entails f1071 [c296, c90, c312, c327, c1068, c117, c23, c51, c104, c337, c247, c351, c291, c289, c366] c1071 unsat1071 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c1068 := derived1068 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c351 := h 350 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1072 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c51, some c104, some c337, some c247, some c351, some c291, some c289, some c366, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1072 : lratChecker f1072 p1072 = .success := by decide +kernel
theorem unsat1072 : Unsatisfiable (PosFin 57) f1072 := by
  apply lratCheckerSound f1072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1072
  · intro a ha; simp [p1072] at ha; subst a; trivial
  · exact checked1072
theorem derived1072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1072 := by
  apply localUnsat_implies_entails f1072 [c23, c51, c104, c337, c247, c351, c291, c289, c366] c1072 unsat1072 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c337 := h 336 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1073 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c117, some c63, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1073 : lratChecker f1073 p1073 = .success := by decide +kernel
theorem unsat1073 : Unsatisfiable (PosFin 57) f1073 := by
  apply lratCheckerSound f1073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1073
  · intro a ha; simp [p1073] at ha; subst a; trivial
  · exact checked1073
theorem derived1073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1073 := by
  apply localUnsat_implies_entails f1073 [c119, c117, c63] c1073 unsat1073 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1074 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨27, by decide⟩, true), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c331, some c296, some c90, some c312, some c317, some c1071, some c1073, some c104, some c1072, some c297, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1074 : lratChecker f1074 p1074 = .success := by decide +kernel
theorem unsat1074 : Unsatisfiable (PosFin 57) f1074 := by
  apply lratCheckerSound f1074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1074
  · intro a ha; simp [p1074] at ha; subst a; trivial
  · exact checked1074
theorem derived1074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1074 := by
  apply localUnsat_implies_entails f1074 [c331, c296, c90, c312, c317, c1071, c1073, c104, c1072, c297] c1074 unsat1074 (by rfl) a
  have h0 : Entails.eval a c331 := h 330 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c1071 := derived1071 a h
  have h6 : Entails.eval a c1073 := derived1073 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c1072 := derived1072 a h
  have h9 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1075 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c277, some c331, some c1070, some c1074, some c133, some c4, some c1069, some c61, some c59, some c700, some c123, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1075 : lratChecker f1075 p1075 = .success := by decide +kernel
theorem unsat1075 : Unsatisfiable (PosFin 57) f1075 := by
  apply lratCheckerSound f1075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1075
  · intro a ha; simp [p1075] at ha; subst a; trivial
  · exact checked1075
theorem derived1075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1075 := by
  apply localUnsat_implies_entails f1075 [c1043, c277, c331, c1070, c1074, c133, c4, c1069, c61, c59, c700, c123] c1075 unsat1075 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c331 := h 330 (by decide)
  have h3 : Entails.eval a c1070 := derived1070 a h
  have h4 : Entails.eval a c1074 := derived1074 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c1069 := derived1069 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c700 := derived700 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1076 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨48, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c248, some c214, some c388, some c195, some c183, some c350, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1076 : lratChecker f1076 p1076 = .success := by decide +kernel
theorem unsat1076 : Unsatisfiable (PosFin 57) f1076 := by
  apply lratCheckerSound f1076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1076
  · intro a ha; simp [p1076] at ha; subst a; trivial
  · exact checked1076
theorem derived1076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1076 := by
  apply localUnsat_implies_entails f1076 [c133, c248, c214, c388, c195, c183, c350] c1076 unsat1076 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1077 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1063, some c277, some c281, some c1064, some c1075, some c126, some c18, some c8, some c52, some c246, some c70, some c274, some c92, some c1076, some c296, some c385, some c104, some c117, some c1073, some c1068, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1077 : lratChecker f1077 p1077 = .success := by decide +kernel
theorem unsat1077 : Unsatisfiable (PosFin 57) f1077 := by
  apply lratCheckerSound f1077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1077
  · intro a ha; simp [p1077] at ha; subst a; trivial
  · exact checked1077
theorem derived1077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1077 := by
  apply localUnsat_implies_entails f1077 [c1043, c1063, c277, c281, c1064, c1075, c126, c18, c8, c52, c246, c70, c274, c92, c1076, c296, c385, c104, c117, c1073, c1068] c1077 unsat1077 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1063 := derived1063 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c1064 := derived1064 a h
  have h5 : Entails.eval a c1075 := derived1075 a h
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c1076 := derived1076 a h
  have h15 : Entails.eval a c296 := h 295 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c104 := h 103 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  have h19 : Entails.eval a c1073 := derived1073 a h
  have h20 : Entails.eval a c1068 := derived1068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1078 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨41, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c1073, some c1068, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1078 : lratChecker f1078 p1078 = .success := by decide +kernel
theorem unsat1078 : Unsatisfiable (PosFin 57) f1078 := by
  apply lratCheckerSound f1078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1078
  · intro a ha; simp [p1078] at ha; subst a; trivial
  · exact checked1078
theorem derived1078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1078 := by
  apply localUnsat_implies_entails f1078 [c117, c1073, c1068] c1078 unsat1078 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c1073 := derived1073 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1079 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c246, some c50, some c296, some c1078, some c104, some c84, some c297, some c247, some c23, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1079 : lratChecker f1079 p1079 = .success := by decide +kernel
theorem unsat1079 : Unsatisfiable (PosFin 57) f1079 := by
  apply lratCheckerSound f1079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1079
  · intro a ha; simp [p1079] at ha; subst a; trivial
  · exact checked1079
theorem derived1079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1079 := by
  apply localUnsat_implies_entails f1079 [c1043, c246, c50, c296, c1078, c104, c84, c297, c247, c23] c1079 unsat1079 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c1078 := derived1078 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1080 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨46, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c132, some c277, some c160, some c1079, some c133, some c246, some c84, some c247, some c23, some c327, some c170, some c1, some c49, some c102, some c348, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1080 : lratChecker f1080 p1080 = .success := by decide +kernel
theorem unsat1080 : Unsatisfiable (PosFin 57) f1080 := by
  apply lratCheckerSound f1080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1080
  · intro a ha; simp [p1080] at ha; subst a; trivial
  · exact checked1080
theorem derived1080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1080 := by
  apply localUnsat_implies_entails f1080 [c1043, c132, c277, c160, c1079, c133, c246, c84, c247, c23, c327, c170, c1, c49, c102, c348] c1080 unsat1080 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1079 := derived1079 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1081 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨46, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c132, some c277, some c160, some c1079, some c133, some c246, some c70, some c274, some c1080, some c119, some c117, some c3, some c92, some c700, some c159, some c350, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1081 : lratChecker f1081 p1081 = .success := by decide +kernel
theorem unsat1081 : Unsatisfiable (PosFin 57) f1081 := by
  apply lratCheckerSound f1081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1081
  · intro a ha; simp [p1081] at ha; subst a; trivial
  · exact checked1081
theorem derived1081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1081 := by
  apply localUnsat_implies_entails f1081 [c1043, c132, c277, c160, c1079, c133, c246, c70, c274, c1080, c119, c117, c3, c92, c700, c159, c350] c1081 unsat1081 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1079 := derived1079 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c1080 := derived1080 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c700 := derived700 a h
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1082 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1077, some c132, some c277, some c160, some c1079, some c133, some c1081, some c104, some c195, some c3, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1082 : lratChecker f1082 p1082 = .success := by decide +kernel
theorem unsat1082 : Unsatisfiable (PosFin 57) f1082 := by
  apply lratCheckerSound f1082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1082
  · intro a ha; simp [p1082] at ha; subst a; trivial
  · exact checked1082
theorem derived1082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1082 := by
  apply localUnsat_implies_entails f1082 [c1043, c1077, c132, c277, c160, c1079, c133, c1081, c104, c195, c3] c1082 unsat1082 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c1079 := derived1079 a h
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c1081 := derived1081 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1083 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1077, some c160, some c132, some c246, some c277, some c281, some c70, some c274, some c1079, some c248, some c1082, some c388, some c387, some c379, some c250, some c272, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1083 : lratChecker f1083 p1083 = .success := by decide +kernel
theorem unsat1083 : Unsatisfiable (PosFin 57) f1083 := by
  apply lratCheckerSound f1083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1083
  · intro a ha; simp [p1083] at ha; subst a; trivial
  · exact checked1083
theorem derived1083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1083 := by
  apply localUnsat_implies_entails f1083 [c1043, c1077, c160, c132, c246, c277, c281, c70, c274, c1079, c248, c1082, c388, c387, c379, c250, c272] c1083 unsat1083 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c277 := h 276 (by decide)
  have h6 : Entails.eval a c281 := h 280 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c1079 := derived1079 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c1082 := derived1082 a h
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c387 := h 386 (by decide)
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1084 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c246, some c349, some c32, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 57) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c1043, c246, c349, c32] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c32, some c103, some c277, some c295, some c133, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c1043, c32, c103, c277, c295, c133] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨23, by decide⟩, true), (⟨48, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c667, some c233, some c277, some c298, some c329, some c1084, some c72, some c314, some c388, some c507, some c184, some c318, some c717, some c224, some c280, some c681, some c149, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c1043, c667, c233, c277, c298, c329, c1084, c72, c314, c388, c507, c184, c318, c717, c224, c280, c681, c149] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c298 := h 297 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c1084 := derived1084 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c507 := derived507 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c717 := derived717 a h
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c681 := derived681 a h
  have h17 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨49, by decide⟩, true), (⟨33, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c43, some c72, some c83, some c676, some c681, some c370, some c79, some c178, some c11, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1043, c43, c72, c83, c676, c681, c370, c79, c178, c11] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c676 := derived676 a h
  have h5 : Entails.eval a c681 := derived681 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c1083, some c328, some c329, some c158, some c171, some c64, some c119, some c117, some c3, some c62, some c1085, some c667, some c298, some c277, some c731, some c233, some c1086, some c90, some c102, some c261, some c1087, some c368, some c172, some c351, some c396, some c719, some c395, some c185, some c373, some c389, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c1043, c1083, c328, c329, c158, c171, c64, c119, c117, c3, c62, c1085, c667, c298, c277, c731, c233, c1086, c90, c102, c261, c1087, c368, c172, c351, c396, c719, c395, c185, c373, c389] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c1083 := derived1083 a h
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c667 := derived667 a h
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c277 := h 276 (by decide)
  have h15 : Entails.eval a c731 := derived731 a h
  have h16 : Entails.eval a c233 := h 232 (by decide)
  have h17 : Entails.eval a c1086 := derived1086 a h
  have h18 : Entails.eval a c90 := h 89 (by decide)
  have h19 : Entails.eval a c102 := h 101 (by decide)
  have h20 : Entails.eval a c261 := h 260 (by decide)
  have h21 : Entails.eval a c1087 := derived1087 a h
  have h22 : Entails.eval a c368 := h 367 (by decide)
  have h23 : Entails.eval a c172 := h 171 (by decide)
  have h24 : Entails.eval a c351 := h 350 (by decide)
  have h25 : Entails.eval a c396 := h 395 (by decide)
  have h26 : Entails.eval a c719 := derived719 a h
  have h27 : Entails.eval a c395 := h 394 (by decide)
  have h28 : Entails.eval a c185 := h 184 (by decide)
  have h29 : Entails.eval a c373 := h 372 (by decide)
  have h30 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨38, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c117, some c119, some c731, some c233, some c672, some c153, some c3, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 57) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c1043, c117, c119, c731, c233, c672, c153, c3] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c731 := derived731 a h
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c672 := derived672 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨21, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c1088, some c158, some c62, some c1089, some c125, some c3, some c672, some c171, some c283, some c334, some c221, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 57) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c117, c1088, c158, c62, c1089, c125, c3, c672, c171, c283, c334, c221] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c1089 := derived1089 a h
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c672 := derived672 a h
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, true), (⟨21, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c3, some c672, some c195, some c283, some c385, some c390, some c249, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 57) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c125, c3, c672, c195, c283, c385, c390, c249] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c672 := derived672 a h
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c390 := h 389 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1088, some c119, some c117, some c24, some c32, some c43, some c1090, some c309, some c102, some c1091, some c731, some c1089, some c672, some c82, some c3, some c638, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 57) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c1088, c119, c117, c24, c32, c43, c1090, c309, c102, c1091, c731, c1089, c672, c82, c3, c638] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c1088 := derived1088 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c1090 := derived1090 a h
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c1091 := derived1091 a h
  have h10 : Entails.eval a c731 := derived731 a h
  have h11 : Entails.eval a c1089 := derived1089 a h
  have h12 : Entails.eval a c672 := derived672 a h
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c638 := derived638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c90, some c104, some c325, some c310, some c72, some c51, some c350, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 57) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c309, c90, c104, c325, c310, c72, c51, c350] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1094 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c32, some c1093, some c158, some c64, some c310, some c104, some c91, some c1084, some c659, some c72, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 57) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c24, c32, c1093, c158, c64, c310, c104, c91, c1084, c659, c72] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c1093 := derived1093 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c310 := h 309 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c1084 := derived1084 a h
  have h9 : Entails.eval a c659 := derived659 a h
  have h10 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨54, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c384, some c261, some c233, some c507, some c395, some c353, some c373, some c347, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 57) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c1043, c384, c261, c233, c507, c395, c353, c373, c347] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c507 := derived507 a h
  have h5 : Entails.eval a c395 := h 394 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c373 := h 372 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1096 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨49, by decide⟩, false), (⟨20, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨47, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c391, some c361, some c940, some c4, some c149, some c198, some c188, some c370, some c215, some c178, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 57) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c659, c391, c361, c940, c4, c149, c198, c188, c370, c215, c178] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c940 := derived940 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨46, by decide⟩, false), (⟨48, by decide⟩, false), (⟨30, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c384, some c388, some c158, some c1088, some c1095, some c248, some c280, some c266, some c222, some c250, some c507, some c391, some c374, some c306, some c62, some c169, some c125, some c1, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c1043, c384, c388, c158, c1088, c1095, c248, c280, c266, c222, c250, c507, c391, c374, c306, c62, c169, c125, c1] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c1088 := derived1088 a h
  have h5 : Entails.eval a c1095 := derived1095 a h
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c507 := derived507 a h
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c125 := h 124 (by decide)
  have h18 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1043, some c97, some c91, some c31, some c262, some c125, some c248, some c4, some c198, some c280, some c149, some c188, some c250, some c1096, some c6, some c347, some c80, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c1043, c97, c91, c31, c262, c125, c248, c4, c198, c280, c149, c188, c250, c1096, c6, c347, c80] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c1043 := derived1043 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c280 := h 279 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c1096 := derived1096 a h
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c347 := h 346 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1098

end CochromaticTwenty.Certificates.B16_3_2
