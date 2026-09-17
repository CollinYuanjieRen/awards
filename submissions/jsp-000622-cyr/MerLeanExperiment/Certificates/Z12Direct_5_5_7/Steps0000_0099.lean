import MerLeanExperiment.Certificates.Z12Direct_5_5_7.Inputs

/-! Generated from the actual pinned z12direct_5_5_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c219 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c37, some c2, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c56, c37, c2] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c21, some c219, some c36, some c53, some c41, some c58, some c2, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c21, c219, c36, c53, c41, c58, c2] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c219 := derived219 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c220, some c10, some c3, some c81, some c74, some c73, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c220, c10, c3, c81, c74, c73] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c220 := derived220 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c42, some c38, some c36, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c42, c38, c36] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c220, some c222, some c3, some c57, some c59, some c53, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c220, c222, c3, c57, c59, c53] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c220 := derived220 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c220, some c221, some c223, some c2, some c16, some c3, some c75, some c82, some c73, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c220, c221, c223, c2, c16, c3, c75, c82, c73] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c220 := derived220 a h
  have h1 : Entails.eval a c221 := derived221 a h
  have h2 : Entails.eval a c223 := derived223 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c135, some c199, some c93, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c34, c135, c199, c93] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c34, some c148, some c6, some c153, some c201, some c22, some c70, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c225, c34, c148, c6, c153, c201, c22, c70] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c225 := derived225 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c224, some c225, some c34, some c226, some c141, some c24, some c205, some c14, some c142, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c75, c224, c225, c34, c226, c141, c24, c205, c14, c142] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c226 := derived226 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c228 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c225, some c34, some c75, some c227, some c12, some c1, some c201, some c61, some c62, some c71, some c60, some c52, some c214, some c170, some c195, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked228 : lratChecker f228 p228 = .success := by decide +kernel
theorem unsat228 : Unsatisfiable (PosFin 31) f228 := by
  apply lratCheckerSound f228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p228
  · intro a ha; simp [p228] at ha; subst a; trivial
  · exact checked228
theorem derived228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c228 := by
  apply localUnsat_implies_entails f228 [c224, c225, c34, c75, c227, c12, c1, c201, c61, c62, c71, c60, c52, c214, c170, c195] c228 unsat228 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c225 := derived225 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c227 := derived227 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c229 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c34, some c3, some c143, some c18, some c43, some c85, some c22, some c11, some c7, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked229 : lratChecker f229 p229 = .success := by decide +kernel
theorem unsat229 : Unsatisfiable (PosFin 31) f229 := by
  apply lratCheckerSound f229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p229
  · intro a ha; simp [p229] at ha; subst a; trivial
  · exact checked229
theorem derived229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c229 := by
  apply localUnsat_implies_entails f229 [c225, c34, c3, c143, c18, c43, c85, c22, c11, c7] c229 unsat229 (by rfl) a
  have h0 : Entails.eval a c225 := derived225 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c143 := h 142 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c230 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c225, some c34, some c229, some c75, some c228, some c57, some c109, some c114, some c159, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked230 : lratChecker f230 p230 = .success := by decide +kernel
theorem unsat230 : Unsatisfiable (PosFin 31) f230 := by
  apply lratCheckerSound f230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p230
  · intro a ha; simp [p230] at ha; subst a; trivial
  · exact checked230
theorem derived230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c230 := by
  apply localUnsat_implies_entails f230 [c224, c225, c34, c229, c75, c228, c57, c109, c114, c159] c230 unsat230 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c225 := derived225 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c229 := derived229 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c228 := derived228 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c231 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c23, some c1, some c207, some c58, some c65, some c210, some c214, some c32, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked231 : lratChecker f231 p231 = .success := by decide +kernel
theorem unsat231 : Unsatisfiable (PosFin 31) f231 := by
  apply lratCheckerSound f231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p231
  · intro a ha; simp [p231] at ha; subst a; trivial
  · exact checked231
theorem derived231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c231 := by
  apply localUnsat_implies_entails f231 [c224, c23, c1, c207, c58, c65, c210, c214, c32] c231 unsat231 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c232 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c224, some c225, some c230, some c41, some c231, some c1, some c207, some c58, some c6, some c210, some c22, some c70, some c63, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked232 : lratChecker f232 p232 = .success := by decide +kernel
theorem unsat232 : Unsatisfiable (PosFin 31) f232 := by
  apply lratCheckerSound f232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p232
  · intro a ha; simp [p232] at ha; subst a; trivial
  · exact checked232
theorem derived232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c232 := by
  apply localUnsat_implies_entails f232 [c34, c224, c225, c230, c41, c231, c1, c207, c58, c6, c210, c22, c70, c63] c232 unsat232 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c230 := derived230 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c231 := derived231 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c233 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c159, some c214, some c93, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked233 : lratChecker f233 p233 = .success := by decide +kernel
theorem unsat233 : Unsatisfiable (PosFin 31) f233 := by
  apply lratCheckerSound f233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p233
  · intro a ha; simp [p233] at ha; subst a; trivial
  · exact checked233
theorem derived233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c233 := by
  apply localUnsat_implies_entails f233 [c34, c159, c214, c93] c233 unsat233 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c234 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c34, some c225, some c233, some c32, some c24, some c230, some c232, some c47, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked234 : lratChecker f234 p234 = .success := by decide +kernel
theorem unsat234 : Unsatisfiable (PosFin 31) f234 := by
  apply lratCheckerSound f234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p234
  · intro a ha; simp [p234] at ha; subst a; trivial
  · exact checked234
theorem derived234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c234 := by
  apply localUnsat_implies_entails f234 [c224, c34, c225, c233, c32, c24, c230, c232, c47] c234 unsat234 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c233 := derived233 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c230 := derived230 a h
  have h7 : Entails.eval a c232 := derived232 a h
  have h8 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c235 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c32, some c24, some c19, some c2, some c58, some c66, some c105, some c183, some c203, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked235 : lratChecker f235 p235 = .success := by decide +kernel
theorem unsat235 : Unsatisfiable (PosFin 31) f235 := by
  apply lratCheckerSound f235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p235
  · intro a ha; simp [p235] at ha; subst a; trivial
  · exact checked235
theorem derived235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c235 := by
  apply localUnsat_implies_entails f235 [c224, c32, c24, c19, c2, c58, c66, c105, c183, c203] c235 unsat235 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c236 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨16, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c12, some c81, some c3, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked236 : lratChecker f236 p236 = .success := by decide +kernel
theorem unsat236 : Unsatisfiable (PosFin 31) f236 := by
  apply lratCheckerSound f236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p236
  · intro a ha; simp [p236] at ha; subst a; trivial
  · exact checked236
theorem derived236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c236 := by
  apply localUnsat_implies_entails f236 [c12, c81, c3] c236 unsat236 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c237 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c224, some c225, some c233, some c32, some c34, some c138, some c160, some c22, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked237 : lratChecker f237 p237 = .success := by decide +kernel
theorem unsat237 : Unsatisfiable (PosFin 31) f237 := by
  apply lratCheckerSound f237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p237
  · intro a ha; simp [p237] at ha; subst a; trivial
  · exact checked237
theorem derived237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c237 := by
  apply localUnsat_implies_entails f237 [c234, c224, c225, c233, c32, c34, c138, c160, c22] c237 unsat237 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c233 := derived233 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c238 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c224, some c34, some c225, some c233, some c32, some c24, some c235, some c237, some c8, some c143, some c145, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked238 : lratChecker f238 p238 = .success := by decide +kernel
theorem unsat238 : Unsatisfiable (PosFin 31) f238 := by
  apply lratCheckerSound f238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p238
  · intro a ha; simp [p238] at ha; subst a; trivial
  · exact checked238
theorem derived238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c238 := by
  apply localUnsat_implies_entails f238 [c234, c224, c34, c225, c233, c32, c24, c235, c237, c8, c143, c145] c238 unsat238 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c225 := derived225 a h
  have h4 : Entails.eval a c233 := derived233 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c235 := derived235 a h
  have h8 : Entails.eval a c237 := derived237 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c239 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c143, some c145, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked239 : lratChecker f239 p239 = .success := by decide +kernel
theorem unsat239 : Unsatisfiable (PosFin 31) f239 := by
  apply lratCheckerSound f239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p239
  · intro a ha; simp [p239] at ha; subst a; trivial
  · exact checked239
theorem derived239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c239 := by
  apply localUnsat_implies_entails f239 [c143, c145] c239 unsat239 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c240 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c92, some c204, some c173, some c57, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked240 : lratChecker f240 p240 = .success := by decide +kernel
theorem unsat240 : Unsatisfiable (PosFin 31) f240 := by
  apply lratCheckerSound f240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p240
  · intro a ha; simp [p240] at ha; subst a; trivial
  · exact checked240
theorem derived240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c240 := by
  apply localUnsat_implies_entails f240 [c92, c204, c173, c57] c240 unsat240 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c241 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c234, some c224, some c34, some c225, some c233, some c32, some c24, some c237, some c236, some c239, some c240, some c182, some c146, some c206, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked241 : lratChecker f241 p241 = .success := by decide +kernel
theorem unsat241 : Unsatisfiable (PosFin 31) f241 := by
  apply lratCheckerSound f241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p241
  · intro a ha; simp [p241] at ha; subst a; trivial
  · exact checked241
theorem derived241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c241 := by
  apply localUnsat_implies_entails f241 [c238, c234, c224, c34, c225, c233, c32, c24, c237, c236, c239, c240, c182, c146, c206] c241 unsat241 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c234 := derived234 a h
  have h2 : Entails.eval a c224 := derived224 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c225 := derived225 a h
  have h5 : Entails.eval a c233 := derived233 a h
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c237 := derived237 a h
  have h9 : Entails.eval a c236 := derived236 a h
  have h10 : Entails.eval a c239 := derived239 a h
  have h11 : Entails.eval a c240 := derived240 a h
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c242 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c58, some c66, some c182, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked242 : lratChecker f242 p242 = .success := by decide +kernel
theorem unsat242 : Unsatisfiable (PosFin 31) f242 := by
  apply lratCheckerSound f242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p242
  · intro a ha; simp [p242] at ha; subst a; trivial
  · exact checked242
theorem derived242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c242 := by
  apply localUnsat_implies_entails f242 [c58, c66, c182] c242 unsat242 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c243 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, false), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c2, some c137, some c23, some c202, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked243 : lratChecker f243 p243 = .success := by decide +kernel
theorem unsat243 : Unsatisfiable (PosFin 31) f243 := by
  apply lratCheckerSound f243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p243
  · intro a ha; simp [p243] at ha; subst a; trivial
  · exact checked243
theorem derived243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c243 := by
  apply localUnsat_implies_entails f243 [c2, c137, c23, c202] c243 unsat243 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c244 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c224, some c225, some c233, some c32, some c24, some c234, some c238, some c241, some c243, some c58, some c66, some c242, some c105, some c183, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked244 : lratChecker f244 p244 = .success := by decide +kernel
theorem unsat244 : Unsatisfiable (PosFin 31) f244 := by
  apply lratCheckerSound f244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p244
  · intro a ha; simp [p244] at ha; subst a; trivial
  · exact checked244
theorem derived244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c244 := by
  apply localUnsat_implies_entails f244 [c34, c224, c225, c233, c32, c24, c234, c238, c241, c243, c58, c66, c242, c105, c183] c244 unsat244 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c225 := derived225 a h
  have h3 : Entails.eval a c233 := derived233 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c234 := derived234 a h
  have h7 : Entails.eval a c238 := derived238 a h
  have h8 : Entails.eval a c241 := derived241 a h
  have h9 : Entails.eval a c243 := derived243 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c242 := derived242 a h
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c245 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c244, some c34, some c98, some c49, some c83, some c174, some c194, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked245 : lratChecker f245 p245 = .success := by decide +kernel
theorem unsat245 : Unsatisfiable (PosFin 31) f245 := by
  apply lratCheckerSound f245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p245
  · intro a ha; simp [p245] at ha; subst a; trivial
  · exact checked245
theorem derived245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c245 := by
  apply localUnsat_implies_entails f245 [c244, c34, c98, c49, c83, c174, c194] c245 unsat245 (by rfl) a
  have h0 : Entails.eval a c244 := derived244 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c246 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c136, some c2, some c202, some c23, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked246 : lratChecker f246 p246 = .success := by decide +kernel
theorem unsat246 : Unsatisfiable (PosFin 31) f246 := by
  apply lratCheckerSound f246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p246
  · intro a ha; simp [p246] at ha; subst a; trivial
  · exact checked246
theorem derived246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c246 := by
  apply localUnsat_implies_entails f246 [c136, c2, c202, c23] c246 unsat246 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c247 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c244, some c34, some c25, some c93, some c180, some c245, some c68, some c246, some c49, some c116, some c84, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked247 : lratChecker f247 p247 = .success := by decide +kernel
theorem unsat247 : Unsatisfiable (PosFin 31) f247 := by
  apply lratCheckerSound f247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p247
  · intro a ha; simp [p247] at ha; subst a; trivial
  · exact checked247
theorem derived247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c247 := by
  apply localUnsat_implies_entails f247 [c244, c34, c25, c93, c180, c245, c68, c246, c49, c116, c84] c247 unsat247 (by rfl) a
  have h0 : Entails.eval a c244 := derived244 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c245 := derived245 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c246 := derived246 a h
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c248 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c247, some c17, some c244, some c34, some c25, some c93, some c180, some c140, some c151, some c166, some c80, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked248 : lratChecker f248 p248 = .success := by decide +kernel
theorem unsat248 : Unsatisfiable (PosFin 31) f248 := by
  apply lratCheckerSound f248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p248
  · intro a ha; simp [p248] at ha; subst a; trivial
  · exact checked248
theorem derived248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c248 := by
  apply localUnsat_implies_entails f248 [c247, c17, c244, c34, c25, c93, c180, c140, c151, c166, c80] c248 unsat248 (by rfl) a
  have h0 : Entails.eval a c247 := derived247 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c244 := derived244 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c249 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c244, some c34, some c25, some c93, some c180, some c190, some c247, some c248, some c68, some c181, some c117, some c112, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked249 : lratChecker f249 p249 = .success := by decide +kernel
theorem unsat249 : Unsatisfiable (PosFin 31) f249 := by
  apply lratCheckerSound f249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p249
  · intro a ha; simp [p249] at ha; subst a; trivial
  · exact checked249
theorem derived249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c249 := by
  apply localUnsat_implies_entails f249 [c244, c34, c25, c93, c180, c190, c247, c248, c68, c181, c117, c112] c249 unsat249 (by rfl) a
  have h0 : Entails.eval a c244 := derived244 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c247 := derived247 a h
  have h7 : Entails.eval a c248 := derived248 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c181 := h 180 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c250 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c180, some c190, some c32, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked250 : lratChecker f250 p250 = .success := by decide +kernel
theorem unsat250 : Unsatisfiable (PosFin 31) f250 := by
  apply lratCheckerSound f250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p250
  · intro a ha; simp [p250] at ha; subst a; trivial
  · exact checked250
theorem derived250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c250 := by
  apply localUnsat_implies_entails f250 [c180, c190, c32] c250 unsat250 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c251 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c244, some c34, some c250, some c118, some c134, some c158, some c32, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked251 : lratChecker f251 p251 = .success := by decide +kernel
theorem unsat251 : Unsatisfiable (PosFin 31) f251 := by
  apply lratCheckerSound f251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p251
  · intro a ha; simp [p251] at ha; subst a; trivial
  · exact checked251
theorem derived251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c251 := by
  apply localUnsat_implies_entails f251 [c244, c34, c250, c118, c134, c158, c32] c251 unsat251 (by rfl) a
  have h0 : Entails.eval a c244 := derived244 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c250 := derived250 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c252 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c251, some c34, some c24, some c244, some c25, some c93, some c180, some c249, some c17, some c144, some c150, some c175, some c40, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked252 : lratChecker f252 p252 = .success := by decide +kernel
theorem unsat252 : Unsatisfiable (PosFin 31) f252 := by
  apply lratCheckerSound f252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p252
  · intro a ha; simp [p252] at ha; subst a; trivial
  · exact checked252
theorem derived252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c252 := by
  apply localUnsat_implies_entails f252 [c251, c34, c24, c244, c25, c93, c180, c249, c17, c144, c150, c175, c40] c252 unsat252 (by rfl) a
  have h0 : Entails.eval a c251 := derived251 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c244 := derived244 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c249 := derived249 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c150 := h 149 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c253 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c251, some c34, some c152, some c175, some c22, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked253 : lratChecker f253 p253 = .success := by decide +kernel
theorem unsat253 : Unsatisfiable (PosFin 31) f253 := by
  apply lratCheckerSound f253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p253
  · intro a ha; simp [p253] at ha; subst a; trivial
  · exact checked253
theorem derived253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c253 := by
  apply localUnsat_implies_entails f253 [c251, c34, c152, c175, c22] c253 unsat253 (by rfl) a
  have h0 : Entails.eval a c251 := derived251 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c175 := h 174 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c254 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c145, some c184, some c18, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked254 : lratChecker f254 p254 = .success := by decide +kernel
theorem unsat254 : Unsatisfiable (PosFin 31) f254 := by
  apply lratCheckerSound f254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p254
  · intro a ha; simp [p254] at ha; subst a; trivial
  · exact checked254
theorem derived254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c254 := by
  apply localUnsat_implies_entails f254 [c3, c145, c184, c18] c254 unsat254 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c255 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c251, some c34, some c24, some c244, some c25, some c93, some c190, some c249, some c252, some c254, some c152, some c253, some c172, some c39, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked255 : lratChecker f255 p255 = .success := by decide +kernel
theorem unsat255 : Unsatisfiable (PosFin 31) f255 := by
  apply lratCheckerSound f255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p255
  · intro a ha; simp [p255] at ha; subst a; trivial
  · exact checked255
theorem derived255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c255 := by
  apply localUnsat_implies_entails f255 [c251, c34, c24, c244, c25, c93, c190, c249, c252, c254, c152, c253, c172, c39] c255 unsat255 (by rfl) a
  have h0 : Entails.eval a c251 := derived251 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c244 := derived244 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c249 := derived249 a h
  have h8 : Entails.eval a c252 := derived252 a h
  have h9 : Entails.eval a c254 := derived254 a h
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c253 := derived253 a h
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c256 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c251, some c249, some c254, some c244, some c25, some c67, some c59, some c104, some c183, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked256 : lratChecker f256 p256 = .success := by decide +kernel
theorem unsat256 : Unsatisfiable (PosFin 31) f256 := by
  apply lratCheckerSound f256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p256
  · intro a ha; simp [p256] at ha; subst a; trivial
  · exact checked256
theorem derived256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c256 := by
  apply localUnsat_implies_entails f256 [c34, c251, c249, c254, c244, c25, c67, c59, c104, c183] c256 unsat256 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c251 := derived251 a h
  have h2 : Entails.eval a c249 := derived249 a h
  have h3 : Entails.eval a c254 := derived254 a h
  have h4 : Entails.eval a c244 := derived244 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c257 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c251, some c34, some c24, some c244, some c25, some c93, some c190, some c249, some c254, some c256, some c2, some c167, some c217, some c89, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked257 : lratChecker f257 p257 = .success := by decide +kernel
theorem unsat257 : Unsatisfiable (PosFin 31) f257 := by
  apply lratCheckerSound f257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p257
  · intro a ha; simp [p257] at ha; subst a; trivial
  · exact checked257
theorem derived257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c257 := by
  apply localUnsat_implies_entails f257 [c255, c251, c34, c24, c244, c25, c93, c190, c249, c254, c256, c2, c167, c217, c89] c257 unsat257 (by rfl) a
  have h0 : Entails.eval a c255 := derived255 a h
  have h1 : Entails.eval a c251 := derived251 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c244 := derived244 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c249 := derived249 a h
  have h9 : Entails.eval a c254 := derived254 a h
  have h10 : Entails.eval a c256 := derived256 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c258 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c244, some c34, some c251, some c25, some c93, some c180, some c249, some c24, some c255, some c257, some c144, some c140, some c67, some c59, some c181, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked258 : lratChecker f258 p258 = .success := by decide +kernel
theorem unsat258 : Unsatisfiable (PosFin 31) f258 := by
  apply lratCheckerSound f258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p258
  · intro a ha; simp [p258] at ha; subst a; trivial
  · exact checked258
theorem derived258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c258 := by
  apply localUnsat_implies_entails f258 [c244, c34, c251, c25, c93, c180, c249, c24, c255, c257, c144, c140, c67, c59, c181] c258 unsat258 (by rfl) a
  have h0 : Entails.eval a c244 := derived244 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c251 := derived251 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c249 := derived249 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c255 := derived255 a h
  have h9 : Entails.eval a c257 := derived257 a h
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c259 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c244, some c34, some c251, some c25, some c93, some c180, some c17, some c140, some c163, some c91, some c76, some c72, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked259 : lratChecker f259 p259 = .success := by decide +kernel
theorem unsat259 : Unsatisfiable (PosFin 31) f259 := by
  apply lratCheckerSound f259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p259
  · intro a ha; simp [p259] at ha; subst a; trivial
  · exact checked259
theorem derived259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c259 := by
  apply localUnsat_implies_entails f259 [c258, c244, c34, c251, c25, c93, c180, c17, c140, c163, c91, c76, c72] c259 unsat259 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c251 := derived251 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c260 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨4, by decide⟩, false), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c67, some c69, some c64, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked260 : lratChecker f260 p260 = .success := by decide +kernel
theorem unsat260 : Unsatisfiable (PosFin 31) f260 := by
  apply lratCheckerSound f260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p260
  · intro a ha; simp [p260] at ha; subst a; trivial
  · exact checked260
theorem derived260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c260 := by
  apply localUnsat_implies_entails f260 [c67, c69, c64] c260 unsat260 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c261 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c258, some c244, some c34, some c251, some c25, some c93, some c190, some c249, some c259, some c254, some c260, some c2, some c167, some c217, some c89, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked261 : lratChecker f261 p261 = .success := by decide +kernel
theorem unsat261 : Unsatisfiable (PosFin 31) f261 := by
  apply lratCheckerSound f261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p261
  · intro a ha; simp [p261] at ha; subst a; trivial
  · exact checked261
theorem derived261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c261 := by
  apply localUnsat_implies_entails f261 [c258, c244, c34, c251, c25, c93, c190, c249, c259, c254, c260, c2, c167, c217, c89] c261 unsat261 (by rfl) a
  have h0 : Entails.eval a c258 := derived258 a h
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c251 := derived251 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c249 := derived249 a h
  have h8 : Entails.eval a c259 := derived259 a h
  have h9 : Entails.eval a c254 := derived254 a h
  have h10 : Entails.eval a c260 := derived260 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c262 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c34, some c244, some c251, some c25, some c249, some c258, some c261, some c8, some c3, some c254, some c14, some c17, some c168, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked262 : lratChecker f262 p262 = .success := by decide +kernel
theorem unsat262 : Unsatisfiable (PosFin 31) f262 := by
  apply lratCheckerSound f262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p262
  · intro a ha; simp [p262] at ha; subst a; trivial
  · exact checked262
theorem derived262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c262 := by
  apply localUnsat_implies_entails f262 [c34, c244, c251, c25, c249, c258, c261, c8, c3, c254, c14, c17, c168] c262 unsat262 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c251 := derived251 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c249 := derived249 a h
  have h5 : Entails.eval a c258 := derived258 a h
  have h6 : Entails.eval a c261 := derived261 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c254 := derived254 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c263 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c106, some c143, some c54, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked263 : lratChecker f263 p263 = .success := by decide +kernel
theorem unsat263 : Unsatisfiable (PosFin 31) f263 := by
  apply lratCheckerSound f263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p263
  · intro a ha; simp [p263] at ha; subst a; trivial
  · exact checked263
theorem derived263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c263 := by
  apply localUnsat_implies_entails f263 [c106, c143, c54] c263 unsat263 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c264 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c19, some c140, some c68, some c66, some c181, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked264 : lratChecker f264 p264 = .success := by decide +kernel
theorem unsat264 : Unsatisfiable (PosFin 31) f264 := by
  apply lratCheckerSound f264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p264
  · intro a ha; simp [p264] at ha; subst a; trivial
  · exact checked264
theorem derived264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c264 := by
  apply localUnsat_implies_entails f264 [c19, c140, c68, c66, c181] c264 unsat264 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c265 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c95, some c264, some c263, some c8, some c260, some c140, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked265 : lratChecker f265 p265 = .success := by decide +kernel
theorem unsat265 : Unsatisfiable (PosFin 31) f265 := by
  apply lratCheckerSound f265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p265
  · intro a ha; simp [p265] at ha; subst a; trivial
  · exact checked265
theorem derived265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c265 := by
  apply localUnsat_implies_entails f265 [c33, c95, c264, c263, c8, c260, c140] c265 unsat265 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c264 := derived264 a h
  have h3 : Entails.eval a c263 := derived263 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c260 := derived260 a h
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c266 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c265, some c25, some c187, some c250, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked266 : lratChecker f266 p266 = .success := by decide +kernel
theorem unsat266 : Unsatisfiable (PosFin 31) f266 := by
  apply lratCheckerSound f266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p266
  · intro a ha; simp [p266] at ha; subst a; trivial
  · exact checked266
theorem derived266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c266 := by
  apply localUnsat_implies_entails f266 [c265, c25, c187, c250] c266 unsat266 (by rfl) a
  have h0 : Entails.eval a c265 := derived265 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c250 := derived250 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c267 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c260, some c124, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked267 : lratChecker f267 p267 = .success := by decide +kernel
theorem unsat267 : Unsatisfiable (PosFin 31) f267 := by
  apply lratCheckerSound f267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p267
  · intro a ha; simp [p267] at ha; subst a; trivial
  · exact checked267
theorem derived267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c267 := by
  apply localUnsat_implies_entails f267 [c8, c260, c124] c267 unsat267 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c260 := derived260 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c268 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c224, some c120, some c214, some c32, some c97, some c155, some c267, some c263, some c19, some c235, some c124, some c41, some c58, some c99, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked268 : lratChecker f268 p268 = .success := by decide +kernel
theorem unsat268 : Unsatisfiable (PosFin 31) f268 := by
  apply lratCheckerSound f268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p268
  · intro a ha; simp [p268] at ha; subst a; trivial
  · exact checked268
theorem derived268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c268 := by
  apply localUnsat_implies_entails f268 [c266, c224, c120, c214, c32, c97, c155, c267, c263, c19, c235, c124, c41, c58, c99] c268 unsat268 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c267 := derived267 a h
  have h8 : Entails.eval a c263 := derived263 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c235 := derived235 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c269 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c224, some c268, some c211, some c33, some c155, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked269 : lratChecker f269 p269 = .success := by decide +kernel
theorem unsat269 : Unsatisfiable (PosFin 31) f269 := by
  apply lratCheckerSound f269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p269
  · intro a ha; simp [p269] at ha; subst a; trivial
  · exact checked269
theorem derived269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c269 := by
  apply localUnsat_implies_entails f269 [c266, c224, c268, c211, c33, c155] c269 unsat269 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c268 := derived268 a h
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c270 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c211, some c33, some c155, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked270 : lratChecker f270 p270 = .success := by decide +kernel
theorem unsat270 : Unsatisfiable (PosFin 31) f270 := by
  apply lratCheckerSound f270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p270
  · intro a ha; simp [p270] at ha; subst a; trivial
  · exact checked270
theorem derived270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c270 := by
  apply localUnsat_implies_entails f270 [c211, c33, c155] c270 unsat270 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c271 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨28, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c270, some c120, some c214, some c32, some c155, some c97, some c269, some c235, some c103, some c41, some c47, some c126, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked271 : lratChecker f271 p271 = .success := by decide +kernel
theorem unsat271 : Unsatisfiable (PosFin 31) f271 := by
  apply lratCheckerSound f271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p271
  · intro a ha; simp [p271] at ha; subst a; trivial
  · exact checked271
theorem derived271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c271 := by
  apply localUnsat_implies_entails f271 [c224, c270, c120, c214, c32, c155, c97, c269, c235, c103, c41, c47, c126] c271 unsat271 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c270 := derived270 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c269 := derived269 a h
  have h8 : Entails.eval a c235 := derived235 a h
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c272 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c269, some c224, some c270, some c120, some c214, some c32, some c155, some c271, some c254, some c8, some c260, some c2, some c205, some c75, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked272 : lratChecker f272 p272 = .success := by decide +kernel
theorem unsat272 : Unsatisfiable (PosFin 31) f272 := by
  apply lratCheckerSound f272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p272
  · intro a ha; simp [p272] at ha; subst a; trivial
  · exact checked272
theorem derived272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c272 := by
  apply localUnsat_implies_entails f272 [c269, c224, c270, c120, c214, c32, c155, c271, c254, c8, c260, c2, c205, c75] c272 unsat272 (by rfl) a
  have h0 : Entails.eval a c269 := derived269 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c214 := h 213 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c271 := derived271 a h
  have h8 : Entails.eval a c254 := derived254 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c260 := derived260 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c273 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c260, some c2, some c205, some c89, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked273 : lratChecker f273 p273 = .success := by decide +kernel
theorem unsat273 : Unsatisfiable (PosFin 31) f273 := by
  apply lratCheckerSound f273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p273
  · intro a ha; simp [p273] at ha; subst a; trivial
  · exact checked273
theorem derived273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c273 := by
  apply localUnsat_implies_entails f273 [c8, c260, c2, c205, c89] c273 unsat273 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c260 := derived260 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c274 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c272, some c25, some c269, some c273, some c254, some c19, some c33, some c190, some c95, some c139, some c9, some c147, some c169, some c85, some c130, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked274 : lratChecker f274 p274 = .success := by decide +kernel
theorem unsat274 : Unsatisfiable (PosFin 31) f274 := by
  apply lratCheckerSound f274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p274
  · intro a ha; simp [p274] at ha; subst a; trivial
  · exact checked274
theorem derived274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c274 := by
  apply localUnsat_implies_entails f274 [c262, c272, c25, c269, c273, c254, c19, c33, c190, c95, c139, c9, c147, c169, c85, c130] c274 unsat274 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c272 := derived272 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c269 := derived269 a h
  have h4 : Entails.eval a c273 := derived273 a h
  have h5 : Entails.eval a c254 := derived254 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c275 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c272, some c269, some c25, some c33, some c95, some c190, some c273, some c254, some c19, some c274, some c122, some c219, some c103, some c127, some c113, some c129, some c130, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked275 : lratChecker f275 p275 = .success := by decide +kernel
theorem unsat275 : Unsatisfiable (PosFin 31) f275 := by
  apply lratCheckerSound f275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p275
  · intro a ha; simp [p275] at ha; subst a; trivial
  · exact checked275
theorem derived275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c275 := by
  apply localUnsat_implies_entails f275 [c262, c272, c269, c25, c33, c95, c190, c273, c254, c19, c274, c122, c219, c103, c127, c113, c129, c130] c275 unsat275 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c272 := derived272 a h
  have h2 : Entails.eval a c269 := derived269 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c273 := derived273 a h
  have h8 : Entails.eval a c254 := derived254 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c274 := derived274 a h
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c219 := derived219 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c129 := h 128 (by decide)
  have h17 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c276 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c272, some c275, some c187, some c250, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked276 : lratChecker f276 p276 = .success := by decide +kernel
theorem unsat276 : Unsatisfiable (PosFin 31) f276 := by
  apply lratCheckerSound f276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p276
  · intro a ha; simp [p276] at ha; subst a; trivial
  · exact checked276
theorem derived276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c276 := by
  apply localUnsat_implies_entails f276 [c262, c272, c275, c187, c250] c276 unsat276 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c272 := derived272 a h
  have h2 : Entails.eval a c275 := derived275 a h
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c250 := derived250 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c277 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c154, some c187, some c250, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked277 : lratChecker f277 p277 = .success := by decide +kernel
theorem unsat277 : Unsatisfiable (PosFin 31) f277 := by
  apply lratCheckerSound f277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p277
  · intro a ha; simp [p277] at ha; subst a; trivial
  · exact checked277
theorem derived277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c277 := by
  apply localUnsat_implies_entails f277 [c154, c187, c250] c277 unsat277 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c250 := derived250 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c278 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c277, some c224, some c24, some c28, some c211, some c32, some c120, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked278 : lratChecker f278 p278 = .success := by decide +kernel
theorem unsat278 : Unsatisfiable (PosFin 31) f278 := by
  apply lratCheckerSound f278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p278
  · intro a ha; simp [p278] at ha; subst a; trivial
  · exact checked278
theorem derived278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c278 := by
  apply localUnsat_implies_entails f278 [c277, c224, c24, c28, c211, c32, c120] c278 unsat278 (by rfl) a
  have h0 : Entails.eval a c277 := derived277 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c279 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c276, some c278, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked279 : lratChecker f279 p279 = .success := by decide +kernel
theorem unsat279 : Unsatisfiable (PosFin 31) f279 := by
  apply lratCheckerSound f279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p279
  · intro a ha; simp [p279] at ha; subst a; trivial
  · exact checked279
theorem derived279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c279 := by
  apply localUnsat_implies_entails f279 [c262, c276, c278] c279 unsat279 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c278 := derived278 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c280 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c211, some c32, some c120, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked280 : lratChecker f280 p280 = .success := by decide +kernel
theorem unsat280 : Unsatisfiable (PosFin 31) f280 := by
  apply lratCheckerSound f280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p280
  · intro a ha; simp [p280] at ha; subst a; trivial
  · exact checked280
theorem derived280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c280 := by
  apply localUnsat_implies_entails f280 [c211, c32, c120] c280 unsat280 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c281 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c279, some c262, some c224, some c28, some c280, some c212, some c97, some c200, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked281 : lratChecker f281 p281 = .success := by decide +kernel
theorem unsat281 : Unsatisfiable (PosFin 31) f281 := by
  apply lratCheckerSound f281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p281
  · intro a ha; simp [p281] at ha; subst a; trivial
  · exact checked281
theorem derived281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c281 := by
  apply localUnsat_implies_entails f281 [c279, c262, c224, c28, c280, c212, c97, c200] c281 unsat281 (by rfl) a
  have h0 : Entails.eval a c279 := derived279 a h
  have h1 : Entails.eval a c262 := derived262 a h
  have h2 : Entails.eval a c224 := derived224 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c280 := derived280 a h
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c282 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c279, some c262, some c281, some c154, some c187, some c95, some c32, some c26, some c215, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked282 : lratChecker f282 p282 = .success := by decide +kernel
theorem unsat282 : Unsatisfiable (PosFin 31) f282 := by
  apply lratCheckerSound f282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p282
  · intro a ha; simp [p282] at ha; subst a; trivial
  · exact checked282
theorem derived282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c282 := by
  apply localUnsat_implies_entails f282 [c279, c262, c281, c154, c187, c95, c32, c26, c215] c282 unsat282 (by rfl) a
  have h0 : Entails.eval a c279 := derived279 a h
  have h1 : Entails.eval a c262 := derived262 a h
  have h2 : Entails.eval a c281 := derived281 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c283 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c279, some c282, some c198, some c133, some c262, some c30, some c95, some c32, some c155, some c188, some c122, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked283 : lratChecker f283 p283 = .success := by decide +kernel
theorem unsat283 : Unsatisfiable (PosFin 31) f283 := by
  apply lratCheckerSound f283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p283
  · intro a ha; simp [p283] at ha; subst a; trivial
  · exact checked283
theorem derived283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c283 := by
  apply localUnsat_implies_entails f283 [c279, c282, c198, c133, c262, c30, c95, c32, c155, c188, c122] c283 unsat283 (by rfl) a
  have h0 : Entails.eval a c279 := derived279 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c262 := derived262 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c284 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c262, some c279, some c282, some c133, some c198, some c283, some c224, some c155, some c120, some c280, some c179, some c26, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked284 : lratChecker f284 p284 = .success := by decide +kernel
theorem unsat284 : Unsatisfiable (PosFin 31) f284 := by
  apply lratCheckerSound f284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p284
  · intro a ha; simp [p284] at ha; subst a; trivial
  · exact checked284
theorem derived284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c284 := by
  apply localUnsat_implies_entails f284 [c262, c279, c282, c133, c198, c283, c224, c155, c120, c280, c179, c26] c284 unsat284 (by rfl) a
  have h0 : Entails.eval a c262 := derived262 a h
  have h1 : Entails.eval a c279 := derived279 a h
  have h2 : Entails.eval a c282 := derived282 a h
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c283 := derived283 a h
  have h6 : Entails.eval a c224 := derived224 a h
  have h7 : Entails.eval a c155 := h 154 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c280 := derived280 a h
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c285 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c196, some c280, some c119, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked285 : lratChecker f285 p285 = .success := by decide +kernel
theorem unsat285 : Unsatisfiable (PosFin 31) f285 := by
  apply lratCheckerSound f285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p285
  · intro a ha; simp [p285] at ha; subst a; trivial
  · exact checked285
theorem derived285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c285 := by
  apply localUnsat_implies_entails f285 [c284, c196, c280, c119] c285 unsat285 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c280 := derived280 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c286 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c28, some c119, some c270, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked286 : lratChecker f286 p286 = .success := by decide +kernel
theorem unsat286 : Unsatisfiable (PosFin 31) f286 := by
  apply lratCheckerSound f286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p286
  · intro a ha; simp [p286] at ha; subst a; trivial
  · exact checked286
theorem derived286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c286 := by
  apply localUnsat_implies_entails f286 [c284, c28, c119, c270] c286 unsat286 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c270 := derived270 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c287 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c224, some c29, some c197, some c97, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked287 : lratChecker f287 p287 = .success := by decide +kernel
theorem unsat287 : Unsatisfiable (PosFin 31) f287 := by
  apply lratCheckerSound f287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p287
  · intro a ha; simp [p287] at ha; subst a; trivial
  · exact checked287
theorem derived287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c287 := by
  apply localUnsat_implies_entails f287 [c284, c224, c29, c197, c97] c287 unsat287 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c288 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c100, some c5, some c108, some c9, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked288 : lratChecker f288 p288 = .success := by decide +kernel
theorem unsat288 : Unsatisfiable (PosFin 31) f288 := by
  apply lratCheckerSound f288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p288
  · intro a ha; simp [p288] at ha; subst a; trivial
  · exact checked288
theorem derived288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c288 := by
  apply localUnsat_implies_entails f288 [c284, c100, c5, c108, c9] c288 unsat288 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c289 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c224, some c286, some c285, some c287, some c270, some c120, some c97, some c272, some c132, some c288, some c14, some c79, some c149, some c55, some c171, some c209, some c186, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked289 : lratChecker f289 p289 = .success := by decide +kernel
theorem unsat289 : Unsatisfiable (PosFin 31) f289 := by
  apply lratCheckerSound f289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p289
  · intro a ha; simp [p289] at ha; subst a; trivial
  · exact checked289
theorem derived289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c289 := by
  apply localUnsat_implies_entails f289 [c284, c224, c286, c285, c287, c270, c120, c97, c272, c132, c288, c14, c79, c149, c55, c171, c209, c186] c289 unsat289 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c286 := derived286 a h
  have h3 : Entails.eval a c285 := derived285 a h
  have h4 : Entails.eval a c287 := derived287 a h
  have h5 : Entails.eval a c270 := derived270 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c272 := derived272 a h
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c288 := derived288 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c171 := h 170 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c290 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c224, some c286, some c285, some c287, some c270, some c120, some c97, some c272, some c132, some c289, some c8, some c260, some c111, some c123, some c2, some c20, some c115, some c208, some c218, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked290 : lratChecker f290 p290 = .success := by decide +kernel
theorem unsat290 : Unsatisfiable (PosFin 31) f290 := by
  apply lratCheckerSound f290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p290
  · intro a ha; simp [p290] at ha; subst a; trivial
  · exact checked290
theorem derived290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c290 := by
  apply localUnsat_implies_entails f290 [c284, c224, c286, c285, c287, c270, c120, c97, c272, c132, c289, c8, c260, c111, c123, c2, c20, c115, c208, c218] c290 unsat290 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c286 := derived286 a h
  have h3 : Entails.eval a c285 := derived285 a h
  have h4 : Entails.eval a c287 := derived287 a h
  have h5 : Entails.eval a c270 := derived270 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c272 := derived272 a h
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c289 := derived289 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c260 := derived260 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c20 := h 19 (by decide)
  have h17 : Entails.eval a c115 := h 114 (by decide)
  have h18 : Entails.eval a c208 := h 207 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c291 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c224, some c285, some c132, some c286, some c287, some c270, some c120, some c97, some c290, some c15, some c267, some c106, some c101, some c91, some c90, some c86, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked291 : lratChecker f291 p291 = .success := by decide +kernel
theorem unsat291 : Unsatisfiable (PosFin 31) f291 := by
  apply lratCheckerSound f291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p291
  · intro a ha; simp [p291] at ha; subst a; trivial
  · exact checked291
theorem derived291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c291 := by
  apply localUnsat_implies_entails f291 [c284, c224, c285, c132, c286, c287, c270, c120, c97, c290, c15, c267, c106, c101, c91, c90, c86] c291 unsat291 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c224 := derived224 a h
  have h2 : Entails.eval a c285 := derived285 a h
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c286 := derived286 a h
  have h5 : Entails.eval a c287 := derived287 a h
  have h6 : Entails.eval a c270 := derived270 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c290 := derived290 a h
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c267 := derived267 a h
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c292 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c32, some c188, some c291, some c131, some c15, some c267, some c106, some c101, some c91, some c90, some c86, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked292 : lratChecker f292 p292 = .success := by decide +kernel
theorem unsat292 : Unsatisfiable (PosFin 31) f292 := by
  apply lratCheckerSound f292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p292
  · intro a ha; simp [p292] at ha; subst a; trivial
  · exact checked292
theorem derived292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c292 := by
  apply localUnsat_implies_entails f292 [c284, c32, c188, c291, c131, c15, c267, c106, c101, c91, c90, c86] c292 unsat292 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c291 := derived291 a h
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c267 := derived267 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c293 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c291, some c95, some c292, some c32, some c188, some c131, some c288, some c14, some c79, some c77, some c87, some c64, some c50, some c51, some c44, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked293 : lratChecker f293 p293 = .success := by decide +kernel
theorem unsat293 : Unsatisfiable (PosFin 31) f293 := by
  apply lratCheckerSound f293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p293
  · intro a ha; simp [p293] at ha; subst a; trivial
  · exact checked293
theorem derived293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c293 := by
  apply localUnsat_implies_entails f293 [c284, c291, c95, c292, c32, c188, c131, c288, c14, c79, c77, c87, c64, c50, c51, c44] c293 unsat293 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c291 := derived291 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c292 := derived292 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c288 := derived288 a h
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c294 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c291, some c95, some c32, some c131, some c188, some c292, some c293, some c8, some c260, some c111, some c123, some c20, some c110, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked294 : lratChecker f294 p294 = .success := by decide +kernel
theorem unsat294 : Unsatisfiable (PosFin 31) f294 := by
  apply lratCheckerSound f294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p294
  · intro a ha; simp [p294] at ha; subst a; trivial
  · exact checked294
theorem derived294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c294 := by
  apply localUnsat_implies_entails f294 [c284, c291, c95, c32, c131, c188, c292, c293, c8, c260, c111, c123, c20, c110] c294 unsat294 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c291 := derived291 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c292 := derived292 a h
  have h7 : Entails.eval a c293 := derived293 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c260 := derived260 a h
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c295 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c32, some c122, some c132, some c8, some c260, some c273, some c185, some c216, some c20, some c193, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked295 : lratChecker f295 p295 = .success := by decide +kernel
theorem unsat295 : Unsatisfiable (PosFin 31) f295 := by
  apply lratCheckerSound f295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p295
  · intro a ha; simp [p295] at ha; subst a; trivial
  · exact checked295
theorem derived295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c295 := by
  apply localUnsat_implies_entails f295 [c284, c32, c122, c132, c8, c260, c273, c185, c216, c20, c193] c295 unsat295 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c260 := derived260 a h
  have h6 : Entails.eval a c273 := derived273 a h
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c296 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c295, some c32, some c122, some c132, some c20, some c13, some c14, some c161, some c191, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked296 : lratChecker f296 p296 = .success := by decide +kernel
theorem unsat296 : Unsatisfiable (PosFin 31) f296 := by
  apply lratCheckerSound f296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p296
  · intro a ha; simp [p296] at ha; subst a; trivial
  · exact checked296
theorem derived296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c296 := by
  apply localUnsat_implies_entails f296 [c284, c295, c32, c122, c132, c20, c13, c14, c161, c191] c296 unsat296 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c295 := derived295 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c297 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c45, some c162, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked297 : lratChecker f297 p297 = .success := by decide +kernel
theorem unsat297 : Unsatisfiable (PosFin 31) f297 := by
  apply lratCheckerSound f297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p297
  · intro a ha; simp [p297] at ha; subst a; trivial
  · exact checked297
theorem derived297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c297 := by
  apply localUnsat_implies_entails f297 [c45, c162] c297 unsat297 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c298 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c295, some c32, some c122, some c132, some c296, some c297, some c14, some c128, some c2, some c87, some c88, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked298 : lratChecker f298 p298 = .success := by decide +kernel
theorem unsat298 : Unsatisfiable (PosFin 31) f298 := by
  apply lratCheckerSound f298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p298
  · intro a ha; simp [p298] at ha; subst a; trivial
  · exact checked298
theorem derived298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c298 := by
  apply localUnsat_implies_entails f298 [c284, c295, c32, c122, c132, c296, c297, c14, c128, c2, c87, c88] c298 unsat298 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c295 := derived295 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c296 := derived296 a h
  have h6 : Entails.eval a c297 := derived297 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c299 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c32, some c122, some c132, some c295, some c298, some c19, some c254, some c107, some c192, some c209, some c78, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 31) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c284, c32, c122, c132, c295, c298, c19, c254, c107, c192, c209, c78] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c295 := derived295 a h
  have h5 : Entails.eval a c298 := derived298 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c254 := derived254 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c300 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c91, some c90, some c86, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 31) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c91, c90, c86] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c301 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c291, some c95, some c32, some c131, some c294, some c122, some c132, some c299, some c269, some c15, some c300, some c4, some c165, some c48, some c46, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked301 : lratChecker f301 p301 = .success := by decide +kernel
theorem unsat301 : Unsatisfiable (PosFin 31) f301 := by
  apply lratCheckerSound f301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p301
  · intro a ha; simp [p301] at ha; subst a; trivial
  · exact checked301
theorem derived301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c301 := by
  apply localUnsat_implies_entails f301 [c284, c291, c95, c32, c131, c294, c122, c132, c299, c269, c15, c300, c4, c165, c48, c46] c301 unsat301 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c291 := derived291 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c294 := derived294 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c299 := derived299 a h
  have h9 : Entails.eval a c269 := derived269 a h
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c300 := derived300 a h
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c302 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c291, some c301, some c177, some c131, some c270, some c33, some c31, some c178, some c122, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked302 : lratChecker f302 p302 = .success := by decide +kernel
theorem unsat302 : Unsatisfiable (PosFin 31) f302 := by
  apply lratCheckerSound f302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p302
  · intro a ha; simp [p302] at ha; subst a; trivial
  · exact checked302
theorem derived302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c302 := by
  apply localUnsat_implies_entails f302 [c284, c291, c301, c177, c131, c270, c33, c31, c178, c122] c302 unsat302 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c291 := derived291 a h
  have h2 : Entails.eval a c301 := derived301 a h
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c270 := derived270 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c303 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c30, some c94, some c33, some c177, some c131, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked303 : lratChecker f303 p303 = .success := by decide +kernel
theorem unsat303 : Unsatisfiable (PosFin 31) f303 := by
  apply lratCheckerSound f303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p303
  · intro a ha; simp [p303] at ha; subst a; trivial
  · exact checked303
theorem derived303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c303 := by
  apply localUnsat_implies_entails f303 [c284, c30, c94, c33, c177, c131] c303 unsat303 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c177 := h 176 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c304 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c291, some c302, some c303, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked304 : lratChecker f304 p304 = .success := by decide +kernel
theorem unsat304 : Unsatisfiable (PosFin 31) f304 := by
  apply lratCheckerSound f304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p304
  · intro a ha; simp [p304] at ha; subst a; trivial
  · exact checked304
theorem derived304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c304 := by
  apply localUnsat_implies_entails f304 [c291, c302, c303] c304 unsat304 (by rfl) a
  have h0 : Entails.eval a c291 := derived291 a h
  have h1 : Entails.eval a c302 := derived302 a h
  have h2 : Entails.eval a c303 := derived303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c305 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c121, some c215, some c158, some c224, some c196, some c24, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked305 : lratChecker f305 p305 = .success := by decide +kernel
theorem unsat305 : Unsatisfiable (PosFin 31) f305 := by
  apply lratCheckerSound f305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p305
  · intro a ha; simp [p305] at ha; subst a; trivial
  · exact checked305
theorem derived305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c305 := by
  apply localUnsat_implies_entails f305 [c284, c121, c215, c158, c224, c196, c24] c305 unsat305 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c224 := derived224 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c306 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c304, some c305, some c33, some c213, some c96, some c159, some c35, some c177, some c25, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked306 : lratChecker f306 p306 = .success := by decide +kernel
theorem unsat306 : Unsatisfiable (PosFin 31) f306 := by
  apply lratCheckerSound f306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p306
  · intro a ha; simp [p306] at ha; subst a; trivial
  · exact checked306
theorem derived306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c306 := by
  apply localUnsat_implies_entails f306 [c284, c304, c305, c33, c213, c96, c159, c35, c177, c25] c306 unsat306 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c304 := derived304 a h
  have h2 : Entails.eval a c305 := derived305 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c307 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c94, some c119, some c224, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked307 : lratChecker f307 p307 = .success := by decide +kernel
theorem unsat307 : Unsatisfiable (PosFin 31) f307 := by
  apply lratCheckerSound f307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p307
  · intro a ha; simp [p307] at ha; subst a; trivial
  · exact checked307
theorem derived307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c307 := by
  apply localUnsat_implies_entails f307 [c284, c94, c119, c224] c307 unsat307 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c224 := derived224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c308 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c306, some c307, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked308 : lratChecker f308 p308 = .success := by decide +kernel
theorem unsat308 : Unsatisfiable (PosFin 31) f308 := by
  apply lratCheckerSound f308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p308
  · intro a ha; simp [p308] at ha; subst a; trivial
  · exact checked308
theorem derived308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c308 := by
  apply localUnsat_implies_entails f308 [c306, c307] c308 unsat308 (by rfl) a
  have h0 : Entails.eval a c306 := derived306 a h
  have h1 : Entails.eval a c307 := derived307 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c309 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c308, some c15, some c300, some c101, some c102, some c4, some c20, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked309 : lratChecker f309 p309 = .success := by decide +kernel
theorem unsat309 : Unsatisfiable (PosFin 31) f309 := by
  apply lratCheckerSound f309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p309
  · intro a ha; simp [p309] at ha; subst a; trivial
  · exact checked309
theorem derived309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c309 := by
  apply localUnsat_implies_entails f309 [c284, c308, c15, c300, c101, c102, c4, c20] c309 unsat309 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c308 := derived308 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c300 := derived300 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c310 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f310 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c304, some c308, some c224, some c132, some c157, some c199, some c97, some c309, some c273, some c288, some c254, some c14, some c235, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p310 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked310 : lratChecker f310 p310 = .success := by decide +kernel
theorem unsat310 : Unsatisfiable (PosFin 31) f310 := by
  apply lratCheckerSound f310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p310
  · intro a ha; simp [p310] at ha; subst a; trivial
  · exact checked310
theorem derived310 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c310 := by
  apply localUnsat_implies_entails f310 [c284, c304, c308, c224, c132, c157, c199, c97, c309, c273, c288, c254, c14, c235] c310 unsat310 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c304 := derived304 a h
  have h2 : Entails.eval a c308 := derived308 a h
  have h3 : Entails.eval a c224 := derived224 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c309 := derived309 a h
  have h9 : Entails.eval a c273 := derived273 a h
  have h10 : Entails.eval a c288 := derived288 a h
  have h11 : Entails.eval a c254 := derived254 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c235 := derived235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c311 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨28, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f311 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c308, some c284, some c32, some c189, some c27, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p311 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked311 : lratChecker f311 p311 = .success := by decide +kernel
theorem unsat311 : Unsatisfiable (PosFin 31) f311 := by
  apply lratCheckerSound f311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p311
  · intro a ha; simp [p311] at ha; subst a; trivial
  · exact checked311
theorem derived311 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c311 := by
  apply localUnsat_implies_entails f311 [c308, c284, c32, c189, c27] c311 unsat311 (by rfl) a
  have h0 : Entails.eval a c308 := derived308 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c312 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f312 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c308, some c311, some c287, some c310, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p312 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked312 : lratChecker f312 p312 = .success := by decide +kernel
theorem unsat312 : Unsatisfiable (PosFin 31) f312 := by
  apply lratCheckerSound f312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p312
  · intro a ha; simp [p312] at ha; subst a; trivial
  · exact checked312
theorem derived312 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c312 := by
  apply localUnsat_implies_entails f312 [c308, c311, c287, c310] c312 unsat312 (by rfl) a
  have h0 : Entails.eval a c308 := derived308 a h
  have h1 : Entails.eval a c311 := derived311 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c310 := derived310 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c313 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f313 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c304, some c284, some c308, some c312, some c131, some c27, some c178, some c309, some c157, some c273, some c288, some c254, some c14, some c19, some c125, some c176, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p313 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked313 : lratChecker f313 p313 = .success := by decide +kernel
theorem unsat313 : Unsatisfiable (PosFin 31) f313 := by
  apply lratCheckerSound f313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p313
  · intro a ha; simp [p313] at ha; subst a; trivial
  · exact checked313
theorem derived313 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c313 := by
  apply localUnsat_implies_entails f313 [c304, c284, c308, c312, c131, c27, c178, c309, c157, c273, c288, c254, c14, c19, c125, c176] c313 unsat313 (by rfl) a
  have h0 : Entails.eval a c304 := derived304 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c308 := derived308 a h
  have h3 : Entails.eval a c312 := derived312 a h
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c309 := derived309 a h
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c273 := derived273 a h
  have h10 : Entails.eval a c288 := derived288 a h
  have h11 : Entails.eval a c254 := derived254 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c314 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨26, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f314 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c308, some c304, some c131, some c122, some c299, some c132, some c15, some c300, some c157, some c164, some c163, some c143, some c140, some c8, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p314 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked314 : lratChecker f314 p314 = .success := by decide +kernel
theorem unsat314 : Unsatisfiable (PosFin 31) f314 := by
  apply lratCheckerSound f314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p314
  · intro a ha; simp [p314] at ha; subst a; trivial
  · exact checked314
theorem derived314 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c314 := by
  apply localUnsat_implies_entails f314 [c284, c308, c304, c131, c122, c299, c132, c15, c300, c157, c164, c163, c143, c140, c8] c314 unsat314 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c308 := derived308 a h
  have h2 : Entails.eval a c304 := derived304 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c299 := derived299 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c300 := derived300 a h
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c315 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f315 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c304, some c312, some c131, some c313, some c314, some c31, some c180, some c157, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p315 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked315 : lratChecker f315 p315 = .success := by decide +kernel
theorem unsat315 : Unsatisfiable (PosFin 31) f315 := by
  apply lratCheckerSound f315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p315
  · intro a ha; simp [p315] at ha; subst a; trivial
  · exact checked315
theorem derived315 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c315 := by
  apply localUnsat_implies_entails f315 [c284, c304, c312, c131, c313, c314, c31, c180, c157] c315 unsat315 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c304 := derived304 a h
  have h2 : Entails.eval a c312 := derived312 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c313 := derived313 a h
  have h5 : Entails.eval a c314 := derived314 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c316 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f316 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c308, some c284, some c304, some c312, some c315, some c32, some c250, some c27, some c31, some c200, some c157, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p316 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked316 : lratChecker f316 p316 = .success := by decide +kernel
theorem unsat316 : Unsatisfiable (PosFin 31) f316 := by
  apply lratCheckerSound f316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p316
  · intro a ha; simp [p316] at ha; subst a; trivial
  · exact checked316
theorem derived316 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c316 := by
  apply localUnsat_implies_entails f316 [c308, c284, c304, c312, c315, c32, c250, c27, c31, c200, c157] c316 unsat316 (by rfl) a
  have h0 : Entails.eval a c308 := derived308 a h
  have h1 : Entails.eval a c284 := derived284 a h
  have h2 : Entails.eval a c304 := derived304 a h
  have h3 : Entails.eval a c312 := derived312 a h
  have h4 : Entails.eval a c315 := derived315 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c250 := derived250 a h
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c317 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f317 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c284, some c316, some c308, some c177, some c196, some c156, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p317 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked317 : lratChecker f317 p317 = .success := by decide +kernel
theorem unsat317 : Unsatisfiable (PosFin 31) f317 := by
  apply lratCheckerSound f317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p317
  · intro a ha; simp [p317] at ha; subst a; trivial
  · exact checked317
theorem derived317 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c317 := by
  apply localUnsat_implies_entails f317 [c284, c316, c308, c177, c196, c156] c317 unsat317 (by rfl) a
  have h0 : Entails.eval a c284 := derived284 a h
  have h1 : Entails.eval a c316 := derived316 a h
  have h2 : Entails.eval a c308 := derived308 a h
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c318 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f318 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c304, some c316, some c284, some c317, some c33, some c213, some c178, some c132, some c25, some c35, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p318 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked318 : lratChecker f318 p318 = .success := by decide +kernel
theorem unsat318 : Unsatisfiable (PosFin 31) f318 := by
  apply lratCheckerSound f318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p318
  · intro a ha; simp [p318] at ha; subst a; trivial
  · exact checked318
theorem derived318 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c318 := by
  apply localUnsat_implies_entails f318 [c304, c316, c284, c317, c33, c213, c178, c132, c25, c35] c318 unsat318 (by rfl) a
  have h0 : Entails.eval a c304 := derived304 a h
  have h1 : Entails.eval a c316 := derived316 a h
  have h2 : Entails.eval a c284 := derived284 a h
  have h3 : Entails.eval a c317 := derived317 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived318

end CochromaticTwenty.Certificates.Z12Direct_5_5_7
