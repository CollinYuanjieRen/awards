import MerLeanExperiment.Certificates.B16_7_2.Steps0500_0599

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c989 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨33, by decide⟩, true), (⟨17, by decide⟩, false), (⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨45, by decide⟩, true), (⟨44, by decide⟩, true), (⟨10, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨31, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c55, some c39, some c145, some c111, some c289, some c263, some c243, some c988, some c77, some c101, some c22, some c52, some c209, some c318, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c48, c55, c39, c145, c111, c289, c263, c243, c988, c77, c101, c22, c52, c209, c318] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c243 := h 242 (by decide)
  have h8 : Entails.eval a c988 := derived988 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨34, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨44, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c66, some c275, some c353, some c45, some c216, some c22, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 57) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c52, c66, c275, c353, c45, c216, c22] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c701, some c55, some c115, some c199, some c196, some c173, some c688, some c109, some c117, some c124, some c319, some c798, some c349, some c346, some c48, some c62, some c191, some c989, some c195, some c153, some c990, some c13, some c18, some c130, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 57) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c39, c701, c55, c115, c199, c196, c173, c688, c109, c117, c124, c319, c798, c349, c346, c48, c62, c191, c989, c195, c153, c990, c13, c18, c130] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c173 := h 172 (by decide)
  have h7 : Entails.eval a c688 := derived688 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c319 := h 318 (by decide)
  have h12 : Entails.eval a c798 := derived798 a h
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  have h18 : Entails.eval a c989 := derived989 a h
  have h19 : Entails.eval a c195 := h 194 (by decide)
  have h20 : Entails.eval a c153 := h 152 (by decide)
  have h21 : Entails.eval a c990 := derived990 a h
  have h22 : Entails.eval a c13 := h 12 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  have h24 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c984, some c983, some c908, some c987, some c991, some c890, some c356, some c12, some c217, some c48, some c176, some c277, some c56, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 57) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c984, c983, c908, c987, c991, c890, c356, c12, c217, c48, c176, c277, c56] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c984 := derived984 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c987 := derived987 a h
  have h4 : Entails.eval a c991 := derived991 a h
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c908, some c984, some c992, some c103, some c48, some c316, some c319, some c204, some c45, some c109, some c946, some c985, some c356, some c277, some c217, some c56, some c176, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 57) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c983, c908, c984, c992, c103, c48, c316, c319, c204, c45, c109, c946, c985, c356, c277, c217, c56, c176] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c984 := derived984 a h
  have h3 : Entails.eval a c992 := derived992 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c946 := derived946 a h
  have h12 : Entails.eval a c985 := derived985 a h
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c277 := h 276 (by decide)
  have h15 : Entails.eval a c217 := h 216 (by decide)
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c126, some c238, some c177, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c126, c238, c177] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c126 := h 125 (by decide)
  have h1 : Entails.eval a c238 := h 237 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨39, by decide⟩, false), (⟨36, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c266, some c229, some c351, some c803, some c223, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c265, c266, c229, c351, c803, c223] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c803 := derived803 a h
  have h5 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨51, by decide⟩, true), (⟨36, by decide⟩, true), (⟨4, by decide⟩, true), (⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c48, some c56, some c293, some c68, some c316, some c45, some c39, some c701, some c993, some c983, some c199, some c187, some c994, some c995, some c106, some c205, some c197, some c8, some c258, some c186, some c93, some c455, some c385, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c908, c48, c56, c293, c68, c316, c45, c39, c701, c993, c983, c199, c187, c994, c995, c106, c205, c197, c8, c258, c186, c93, c455, c385] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c701 := derived701 a h
  have h9 : Entails.eval a c993 := derived993 a h
  have h10 : Entails.eval a c983 := derived983 a h
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c187 := h 186 (by decide)
  have h13 : Entails.eval a c994 := derived994 a h
  have h14 : Entails.eval a c995 := derived995 a h
  have h15 : Entails.eval a c106 := h 105 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c186 := h 185 (by decide)
  have h21 : Entails.eval a c93 := h 92 (by decide)
  have h22 : Entails.eval a c455 := derived455 a h
  have h23 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c997 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨35, by decide⟩, false), (⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c39, some c701, some c993, some c983, some c48, some c316, some c319, some c277, some c68, some c343, some c996, some c144, some c137, some c196, some c381, some c258, some c187, some c182, some c111, some c195, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 57) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c908, c39, c701, c993, c983, c48, c316, c319, c277, c68, c343, c996, c144, c137, c196, c381, c258, c187, c182, c111, c195] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c993 := derived993 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c996 := derived996 a h
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c187 := h 186 (by decide)
  have h18 : Entails.eval a c182 := h 181 (by decide)
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c319, some c45, some c144, some c6, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 57) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c316, c319, c45, c144, c6] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨28, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c701, some c45, some c101, some c6, some c753, some c106, some c40, some c209, some c24, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c39, c701, c45, c101, c6, c753, c106, c40, c209, c24] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c753 := derived753 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c209 := h 208 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c39, some c701, some c993, some c983, some c997, some c103, some c28, some c12, some c998, some c208, some c261, some c258, some c203, some c137, some c191, some c278, some c999, some c273, some c156, some c6, some c197, some c196, some c431, some c65, some c54, some c126, some c420, some c343, some c170, some c289, some c291, some c172, some c91, some c78, some c241, some c31, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c908, c39, c701, c993, c983, c997, c103, c28, c12, c998, c208, c261, c258, c203, c137, c191, c278, c999, c273, c156, c6, c197, c196, c431, c65, c54, c126, c420, c343, c170, c289, c291, c172, c91, c78, c241, c31] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c993 := derived993 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c997 := derived997 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c998 := derived998 a h
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c191 := h 190 (by decide)
  have h16 : Entails.eval a c278 := h 277 (by decide)
  have h17 : Entails.eval a c999 := derived999 a h
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c6 := h 5 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c431 := derived431 a h
  have h24 : Entails.eval a c65 := h 64 (by decide)
  have h25 : Entails.eval a c54 := h 53 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  have h27 : Entails.eval a c420 := derived420 a h
  have h28 : Entails.eval a c343 := h 342 (by decide)
  have h29 : Entails.eval a c170 := h 169 (by decide)
  have h30 : Entails.eval a c289 := h 288 (by decide)
  have h31 : Entails.eval a c291 := h 290 (by decide)
  have h32 : Entails.eval a c172 := h 171 (by decide)
  have h33 : Entails.eval a c91 := h 90 (by decide)
  have h34 : Entails.eval a c78 := h 77 (by decide)
  have h35 : Entails.eval a c241 := h 240 (by decide)
  have h36 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c1000, some c215, some c115, some c173, some c196, some c199, some c908, some c39, some c993, some c103, some c28, some c998, some c216, some c208, some c261, some c258, some c203, some c222, some c137, some c269, some c156, some c353, some c162, some c66, some c13, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c983, c1000, c215, c115, c173, c196, c199, c908, c39, c993, c103, c28, c998, c216, c208, c261, c258, c203, c222, c137, c269, c156, c353, c162, c66, c13] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c1000 := derived1000 a h
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c993 := derived993 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c998 := derived998 a h
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c222 := h 221 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c353 := h 352 (by decide)
  have h23 : Entails.eval a c162 := h 161 (by decide)
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c908, some c1000, some c115, some c199, some c196, some c1001, some c48, some c316, some c319, some c144, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c983, c908, c1000, c115, c199, c196, c1001, c48, c316, c319, c144] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1000 := derived1000 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c1001 := derived1001 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c115, some c295, some c173, some c80, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c215, c115, c295, c173, c80] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c173 := h 172 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨36, by decide⟩, false), (⟨35, by decide⟩, false), (⟨52, by decide⟩, false), (⟨29, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c355, some c137, some c387, some c256, some c640, some c156, some c162, some c196, some c345, some c186, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c352, c355, c137, c387, c256, c640, c156, c162, c196, c345, c186] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c640 := derived640 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨51, by decide⟩, true), (⟨13, by decide⟩, false), (⟨34, by decide⟩, true), (⟨43, by decide⟩, true), (⟨39, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c65, some c68, some c197, some c126, some c186, some c909, some c345, some c72, some c164, some c23, some c193, some c225, some c431, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c199, c65, c68, c197, c126, c186, c909, c345, c72, c164, c23, c193, c225, c431] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c909 := derived909 a h
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c193 := h 192 (by decide)
  have h12 : Entails.eval a c225 := h 224 (by decide)
  have h13 : Entails.eval a c431 := derived431 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1002, some c320, some c993, some c983, some c908, some c936, some c36, some c1003, some c279, some c59, some c68, some c295, some c352, some c65, some c1004, some c341, some c199, some c1005, some c157, some c193, some c122, some c182, some c17, some c245, some c43, some c315, some c49, some c311, some c102, some c701, some c382, some c96, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c1002, c320, c993, c983, c908, c936, c36, c1003, c279, c59, c68, c295, c352, c65, c1004, c341, c199, c1005, c157, c193, c122, c182, c17, c245, c43, c315, c49, c311, c102, c701, c382, c96] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c1002 := derived1002 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c936 := derived936 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c279 := h 278 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c1004 := derived1004 a h
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c1005 := derived1005 a h
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c122 := h 121 (by decide)
  have h21 : Entails.eval a c182 := h 181 (by decide)
  have h22 : Entails.eval a c17 := h 16 (by decide)
  have h23 : Entails.eval a c245 := h 244 (by decide)
  have h24 : Entails.eval a c43 := h 42 (by decide)
  have h25 : Entails.eval a c315 := h 314 (by decide)
  have h26 : Entails.eval a c49 := h 48 (by decide)
  have h27 : Entails.eval a c311 := h 310 (by decide)
  have h28 : Entails.eval a c102 := h 101 (by decide)
  have h29 : Entails.eval a c701 := derived701 a h
  have h30 : Entails.eval a c382 := h 381 (by decide)
  have h31 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1007 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨11, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c320, some c144, some c273, some c156, some c114, some c355, some c216, some c228, some c994, some c261, some c266, some c203, some c209, some c315, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1007 : lratChecker f1007 p1007 = .success := by decide +kernel
theorem unsat1007 : Unsatisfiable (PosFin 57) f1007 := by
  apply lratCheckerSound f1007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1007
  · intro a ha; simp [p1007] at ha; subst a; trivial
  · exact checked1007
theorem derived1007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1007 := by
  apply localUnsat_implies_entails f1007 [c279, c320, c144, c273, c156, c114, c355, c216, c228, c994, c261, c266, c203, c209, c315] c1007 unsat1007 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c994 := derived994 a h
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1008 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨11, by decide⟩, true), (⟨35, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c59, some c295, some c1007, some c6, some c65, some c352, some c228, some c261, some c203, some c234, some c287, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1008 : lratChecker f1008 p1008 = .success := by decide +kernel
theorem unsat1008 : Unsatisfiable (PosFin 57) f1008 := by
  apply lratCheckerSound f1008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1008
  · intro a ha; simp [p1008] at ha; subst a; trivial
  · exact checked1008
theorem derived1008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1008 := by
  apply localUnsat_implies_entails f1008 [c279, c59, c295, c1007, c6, c65, c352, c228, c261, c203, c234, c287] c1008 unsat1008 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c1007 := derived1007 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c234 := h 233 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1009 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨35, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c59, some c295, some c1008, some c316, some c277, some c805, some c216, some c261, some c994, some c234, some c287, some c375, some c201, some c239, some c266, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1009 : lratChecker f1009 p1009 = .success := by decide +kernel
theorem unsat1009 : Unsatisfiable (PosFin 57) f1009 := by
  apply lratCheckerSound f1009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1009
  · intro a ha; simp [p1009] at ha; subst a; trivial
  · exact checked1009
theorem derived1009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1009 := by
  apply localUnsat_implies_entails f1009 [c279, c59, c295, c1008, c316, c277, c805, c216, c261, c994, c234, c287, c375, c201, c239, c266] c1009 unsat1009 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c1008 := derived1008 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c277 := h 276 (by decide)
  have h6 : Entails.eval a c805 := derived805 a h
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c994 := derived994 a h
  have h10 : Entails.eval a c234 := h 233 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c375 := h 374 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c239 := h 238 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1010 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c279, some c59, some c295, some c1009, some c196, some c144, some c316, some c273, some c156, some c355, some c228, some c261, some c203, some c234, some c287, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1010 : lratChecker f1010 p1010 = .success := by decide +kernel
theorem unsat1010 : Unsatisfiable (PosFin 57) f1010 := by
  apply lratCheckerSound f1010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1010
  · intro a ha; simp [p1010] at ha; subst a; trivial
  · exact checked1010
theorem derived1010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1010 := by
  apply localUnsat_implies_entails f1010 [c320, c279, c59, c295, c1009, c196, c144, c316, c273, c156, c355, c228, c261, c203, c234, c287] c1010 unsat1010 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c1009 := derived1009 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c234 := h 233 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1011 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c908, some c993, some c1002, some c320, some c1006, some c103, some c28, some c12, some c1010, some c215, some c115, some c295, some c196, some c173, some c59, some c240, some c144, some c261, some c316, some c203, some c222, some c271, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1011 : lratChecker f1011 p1011 = .success := by decide +kernel
theorem unsat1011 : Unsatisfiable (PosFin 57) f1011 := by
  apply lratCheckerSound f1011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1011
  · intro a ha; simp [p1011] at ha; subst a; trivial
  · exact checked1011
theorem derived1011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1011 := by
  apply localUnsat_implies_entails f1011 [c983, c908, c993, c1002, c320, c1006, c103, c28, c12, c1010, c215, c115, c295, c196, c173, c59, c240, c144, c261, c316, c203, c222, c271] c1011 unsat1011 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c1002 := derived1002 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c1006 := derived1006 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c1010 := derived1010 a h
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c240 := h 239 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c261 := h 260 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c222 := h 221 (by decide)
  have h22 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1012 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c320, some c295, some c109, some c137, some c268, some c267, some c254, some c240, some c293, some c376, some c77, some c237, some c101, some c6, some c66, some c90, some c84, some c144, some c177, some c369, some c150, some c318, some c309, some c209, some c347, some c24, some c67, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1012 : lratChecker f1012 p1012 = .success := by decide +kernel
theorem unsat1012 : Unsatisfiable (PosFin 57) f1012 := by
  apply lratCheckerSound f1012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1012
  · intro a ha; simp [p1012] at ha; subst a; trivial
  · exact checked1012
theorem derived1012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1012 := by
  apply localUnsat_implies_entails f1012 [c55, c320, c295, c109, c137, c268, c267, c254, c240, c293, c376, c77, c237, c101, c6, c66, c90, c84, c144, c177, c369, c150, c318, c309, c209, c347, c24, c67] c1012 unsat1012 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c369 := h 368 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c318 := h 317 (by decide)
  have h23 : Entails.eval a c309 := h 308 (by decide)
  have h24 : Entails.eval a c209 := h 208 (by decide)
  have h25 : Entails.eval a c347 := h 346 (by decide)
  have h26 : Entails.eval a c24 := h 23 (by decide)
  have h27 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1013 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, true), (⟨31, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c267, some c208, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1013 : lratChecker f1013 p1013 = .success := by decide +kernel
theorem unsat1013 : Unsatisfiable (PosFin 57) f1013 := by
  apply lratCheckerSound f1013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1013
  · intro a ha; simp [p1013] at ha; subst a; trivial
  · exact checked1013
theorem derived1013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1013 := by
  apply localUnsat_implies_entails f1013 [c268, c267, c208] c1013 unsat1013 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1014 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c39, some c701, some c55, some c346, some c349, some c191, some c62, some c4, some c98, some c154, some c196, some c173, some c124, some c153, some c990, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1014 : lratChecker f1014 p1014 = .success := by decide +kernel
theorem unsat1014 : Unsatisfiable (PosFin 57) f1014 := by
  apply lratCheckerSound f1014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1014
  · intro a ha; simp [p1014] at ha; subst a; trivial
  · exact checked1014
theorem derived1014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1014 := by
  apply localUnsat_implies_entails f1014 [c117, c39, c701, c55, c346, c349, c191, c62, c4, c98, c154, c196, c173, c124, c153, c990] c1014 unsat1014 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c990 := derived990 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1015 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨10, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c59, some c65, some c157, some c24, some c243, some c131, some c180, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1015 : lratChecker f1015 p1015 = .success := by decide +kernel
theorem unsat1015 : Unsatisfiable (PosFin 57) f1015 := by
  apply lratCheckerSound f1015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1015
  · intro a ha; simp [p1015] at ha; subst a; trivial
  · exact checked1015
theorem derived1015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1015 := by
  apply localUnsat_implies_entails f1015 [c124, c59, c65, c157, c24, c243, c131, c180] c1015 unsat1015 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1016 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨39, by decide⟩, true), (⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c55, some c216, some c353, some c990, some c986, some c13, some c175, some c158, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1016 : lratChecker f1016 p1016 = .success := by decide +kernel
theorem unsat1016 : Unsatisfiable (PosFin 57) f1016 := by
  apply lratCheckerSound f1016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1016
  · intro a ha; simp [p1016] at ha; subst a; trivial
  · exact checked1016
theorem derived1016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1016 := by
  apply localUnsat_implies_entails f1016 [c59, c55, c216, c353, c990, c986, c13, c175, c158] c1016 unsat1016 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c990 := derived990 a h
  have h5 : Entails.eval a c986 := derived986 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1017 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c98, some c158, some c186, some c62, some c86, some c334, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1017 : lratChecker f1017 p1017 = .success := by decide +kernel
theorem unsat1017 : Unsatisfiable (PosFin 57) f1017 := by
  apply lratCheckerSound f1017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1017
  · intro a ha; simp [p1017] at ha; subst a; trivial
  · exact checked1017
theorem derived1017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1017 := by
  apply localUnsat_implies_entails f1017 [c13, c98, c158, c186, c62, c86, c334] c1017 unsat1017 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1018 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c701, some c91, some c1014, some c55, some c124, some c1015, some c1016, some c173, some c1017, some c52, some c66, some c90, some c275, some c339, some c134, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1018 : lratChecker f1018 p1018 = .success := by decide +kernel
theorem unsat1018 : Unsatisfiable (PosFin 57) f1018 := by
  apply lratCheckerSound f1018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1018
  · intro a ha; simp [p1018] at ha; subst a; trivial
  · exact checked1018
theorem derived1018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1018 := by
  apply localUnsat_implies_entails f1018 [c39, c701, c91, c1014, c55, c124, c1015, c1016, c173, c1017, c52, c66, c90, c275, c339, c134] c1018 unsat1018 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c1014 := derived1014 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c1015 := derived1015 a h
  have h7 : Entails.eval a c1016 := derived1016 a h
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c1017 := derived1017 a h
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c275 := h 274 (by decide)
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1019 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨45, by decide⟩, true), (⟨28, by decide⟩, true), (⟨31, by decide⟩, true), (⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c39, some c701, some c208, some c255, some c91, some c1014, some c1018, some c6, some c197, some c196, some c45, some c65, some c158, some c1017, some c275, some c52, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1019 : lratChecker f1019 p1019 = .success := by decide +kernel
theorem unsat1019 : Unsatisfiable (PosFin 57) f1019 := by
  apply lratCheckerSound f1019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1019
  · intro a ha; simp [p1019] at ha; subst a; trivial
  · exact checked1019
theorem derived1019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1019 := by
  apply localUnsat_implies_entails f1019 [c1013, c39, c701, c208, c255, c91, c1014, c1018, c6, c197, c196, c45, c65, c158, c1017, c275, c52] c1019 unsat1019 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c1014 := derived1014 a h
  have h7 : Entails.eval a c1018 := derived1018 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c158 := h 157 (by decide)
  have h14 : Entails.eval a c1017 := derived1017 a h
  have h15 : Entails.eval a c275 := h 274 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1020 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c12, some c103, some c1011, some c908, some c55, some c1012, some c998, some c1013, some c109, some c294, some c1019, some c264, some c810, some c968, some c45, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1020 : lratChecker f1020 p1020 = .success := by decide +kernel
theorem unsat1020 : Unsatisfiable (PosFin 57) f1020 := by
  apply lratCheckerSound f1020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1020
  · intro a ha; simp [p1020] at ha; subst a; trivial
  · exact checked1020
theorem derived1020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1020 := by
  apply localUnsat_implies_entails f1020 [c983, c12, c103, c1011, c908, c55, c1012, c998, c1013, c109, c294, c1019, c264, c810, c968, c45] c1020 unsat1020 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c1011 := derived1011 a h
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c1012 := derived1012 a h
  have h7 : Entails.eval a c998 := derived998 a h
  have h8 : Entails.eval a c1013 := derived1013 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c1019 := derived1019 a h
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c810 := derived810 a h
  have h14 : Entails.eval a c968 := derived968 a h
  have h15 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1021 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c998, some c1013, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1021 : lratChecker f1021 p1021 = .success := by decide +kernel
theorem unsat1021 : Unsatisfiable (PosFin 57) f1021 := by
  apply lratCheckerSound f1021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1021
  · intro a ha; simp [p1021] at ha; subst a; trivial
  · exact checked1021
theorem derived1021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1021 := by
  apply localUnsat_implies_entails f1021 [c998, c1013] c1021 unsat1021 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c1013 := derived1013 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1022 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1011, some c983, some c908, some c12, some c1020, some c890, some c268, some c267, some c1021, some c279, some c228, some c355, some c352, some c156, some c65, some c6, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1022 : lratChecker f1022 p1022 = .success := by decide +kernel
theorem unsat1022 : Unsatisfiable (PosFin 57) f1022 := by
  apply lratCheckerSound f1022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1022
  · intro a ha; simp [p1022] at ha; subst a; trivial
  · exact checked1022
theorem derived1022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1022 := by
  apply localUnsat_implies_entails f1022 [c1011, c983, c908, c12, c1020, c890, c268, c267, c1021, c279, c228, c355, c352, c156, c65, c6] c1022 unsat1022 (by rfl) a
  have h0 : Entails.eval a c1011 := derived1011 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c1020 := derived1020 a h
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c1021 := derived1021 a h
  have h9 : Entails.eval a c279 := h 278 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1023 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨29, by decide⟩, true), (⟨35, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c890, some c1004, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1023 : lratChecker f1023 p1023 = .success := by decide +kernel
theorem unsat1023 : Unsatisfiable (PosFin 57) f1023 := by
  apply lratCheckerSound f1023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1023
  · intro a ha; simp [p1023] at ha; subst a; trivial
  · exact checked1023
theorem derived1023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1023 := by
  apply localUnsat_implies_entails f1023 [c890, c1004] c1023 unsat1023 (by rfl) a
  have h0 : Entails.eval a c890 := derived890 a h
  have h1 : Entails.eval a c1004 := derived1004 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1024 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true), (⟨28, by decide⟩, true), (⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c267, some c119, some c225, some c193, some c804, some c49, some c209, some c24, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1024 : lratChecker f1024 p1024 = .success := by decide +kernel
theorem unsat1024 : Unsatisfiable (PosFin 57) f1024 := by
  apply lratCheckerSound f1024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1024
  · intro a ha; simp [p1024] at ha; subst a; trivial
  · exact checked1024
theorem derived1024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1024 := by
  apply localUnsat_implies_entails f1024 [c268, c267, c119, c225, c193, c804, c49, c209, c24] c1024 unsat1024 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c804 := derived804 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1025 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c279, some c928, some c59, some c68, some c36, some c341, some c355, some c352, some c65, some c1023, some c199, some c1024, some c217, some c178, some c157, some c197, some c164, some c186, some c345, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1025 : lratChecker f1025 p1025 = .success := by decide +kernel
theorem unsat1025 : Unsatisfiable (PosFin 57) f1025 := by
  apply lratCheckerSound f1025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1025
  · intro a ha; simp [p1025] at ha; subst a; trivial
  · exact checked1025
theorem derived1025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1025 := by
  apply localUnsat_implies_entails f1025 [c320, c279, c928, c59, c68, c36, c341, c355, c352, c65, c1023, c199, c1024, c217, c178, c157, c197, c164, c186, c345] c1025 unsat1025 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c928 := derived928 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c1023 := derived1023 a h
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c1024 := derived1024 a h
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1026 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1022, some c908, some c983, some c1011, some c1025, some c48, some c277, some c56, some c293, some c68, some c356, some c39, some c343, some c316, some c45, some c701, some c176, some c217, some c268, some c26, some c205, some c91, some c995, some c102, some c212, some c78, some c297, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1026 : lratChecker f1026 p1026 = .success := by decide +kernel
theorem unsat1026 : Unsatisfiable (PosFin 57) f1026 := by
  apply lratCheckerSound f1026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1026
  · intro a ha; simp [p1026] at ha; subst a; trivial
  · exact checked1026
theorem derived1026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1026 := by
  apply localUnsat_implies_entails f1026 [c1022, c908, c983, c1011, c1025, c48, c277, c56, c293, c68, c356, c39, c343, c316, c45, c701, c176, c217, c268, c26, c205, c91, c995, c102, c212, c78, c297] c1026 unsat1026 (by rfl) a
  have h0 : Entails.eval a c1022 := derived1022 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1011 := derived1011 a h
  have h4 : Entails.eval a c1025 := derived1025 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c701 := derived701 a h
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c217 := h 216 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c91 := h 90 (by decide)
  have h22 : Entails.eval a c995 := derived995 a h
  have h23 : Entails.eval a c102 := h 101 (by decide)
  have h24 : Entails.eval a c212 := h 211 (by decide)
  have h25 : Entails.eval a c78 := h 77 (by decide)
  have h26 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1027 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1022, some c1011, some c983, some c908, some c1025, some c39, some c48, some c701, some c316, some c319, some c277, some c68, some c343, some c1026, some c890, some c137, some c144, some c268, some c381, some c196, some c111, some c182, some c187, some c195, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1027 : lratChecker f1027 p1027 = .success := by decide +kernel
theorem unsat1027 : Unsatisfiable (PosFin 57) f1027 := by
  apply lratCheckerSound f1027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1027
  · intro a ha; simp [p1027] at ha; subst a; trivial
  · exact checked1027
theorem derived1027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1027 := by
  apply localUnsat_implies_entails f1027 [c1022, c1011, c983, c908, c1025, c39, c48, c701, c316, c319, c277, c68, c343, c1026, c890, c137, c144, c268, c381, c196, c111, c182, c187, c195] c1027 unsat1027 (by rfl) a
  have h0 : Entails.eval a c1022 := derived1022 a h
  have h1 : Entails.eval a c1011 := derived1011 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c1025 := derived1025 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c277 := h 276 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c1026 := derived1026 a h
  have h14 : Entails.eval a c890 := derived890 a h
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c381 := h 380 (by decide)
  have h19 : Entails.eval a c196 := h 195 (by decide)
  have h20 : Entails.eval a c111 := h 110 (by decide)
  have h21 : Entails.eval a c182 := h 181 (by decide)
  have h22 : Entails.eval a c187 := h 186 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1028 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨29, by decide⟩, true), (⟨26, by decide⟩, true), (⟨55, by decide⟩, false), (⟨31, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c109, some c137, some c144, some c268, some c254, some c381, some c196, some c111, some c182, some c187, some c195, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1028 : lratChecker f1028 p1028 = .success := by decide +kernel
theorem unsat1028 : Unsatisfiable (PosFin 57) f1028 := by
  apply lratCheckerSound f1028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1028
  · intro a ha; simp [p1028] at ha; subst a; trivial
  · exact checked1028
theorem derived1028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1028 := by
  apply localUnsat_implies_entails f1028 [c701, c109, c137, c144, c268, c254, c381, c196, c111, c182, c187, c195] c1028 unsat1028 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1029 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c1011, some c908, some c39, some c1022, some c48, some c316, some c319, some c1028, some c199, some c45, some c701, some c1027, some c268, some c26, some c111, some c55, some c193, some c293, some c154, some c56, some c80, some c367, some c504, some c91, some c881, some c102, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1029 : lratChecker f1029 p1029 = .success := by decide +kernel
theorem unsat1029 : Unsatisfiable (PosFin 57) f1029 := by
  apply lratCheckerSound f1029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1029
  · intro a ha; simp [p1029] at ha; subst a; trivial
  · exact checked1029
theorem derived1029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1029 := by
  apply localUnsat_implies_entails f1029 [c983, c1011, c908, c39, c1022, c48, c316, c319, c1028, c199, c45, c701, c1027, c268, c26, c111, c55, c193, c293, c154, c56, c80, c367, c504, c91, c881, c102] c1029 unsat1029 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c1011 := derived1011 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1022 := derived1022 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c1028 := derived1028 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c701 := derived701 a h
  have h12 : Entails.eval a c1027 := derived1027 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c367 := h 366 (by decide)
  have h23 : Entails.eval a c504 := derived504 a h
  have h24 : Entails.eval a c91 := h 90 (by decide)
  have h25 : Entails.eval a c881 := derived881 a h
  have h26 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1030 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1027, some c1022, some c1011, some c908, some c39, some c48, some c701, some c316, some c319, some c45, some c1029, some c204, some c21, some c55, some c293, some c56, some c80, some c367, some c945, some c91, some c281, some c102, some c52, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1030 : lratChecker f1030 p1030 = .success := by decide +kernel
theorem unsat1030 : Unsatisfiable (PosFin 57) f1030 := by
  apply lratCheckerSound f1030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1030
  · intro a ha; simp [p1030] at ha; subst a; trivial
  · exact checked1030
theorem derived1030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1030 := by
  apply localUnsat_implies_entails f1030 [c1027, c1022, c1011, c908, c39, c48, c701, c316, c319, c45, c1029, c204, c21, c55, c293, c56, c80, c367, c945, c91, c281, c102, c52] c1030 unsat1030 (by rfl) a
  have h0 : Entails.eval a c1027 := derived1027 a h
  have h1 : Entails.eval a c1022 := derived1022 a h
  have h2 : Entails.eval a c1011 := derived1011 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c701 := derived701 a h
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c1029 := derived1029 a h
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c367 := h 366 (by decide)
  have h18 : Entails.eval a c945 := derived945 a h
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c281 := h 280 (by decide)
  have h21 : Entails.eval a c102 := h 101 (by decide)
  have h22 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1031 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c38, some c251, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1031 : lratChecker f1031 p1031 = .success := by decide +kernel
theorem unsat1031 : Unsatisfiable (PosFin 57) f1031 := by
  apply lratCheckerSound f1031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1031
  · intro a ha; simp [p1031] at ha; subst a; trivial
  · exact checked1031
theorem derived1031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1031 := by
  apply localUnsat_implies_entails f1031 [c210, c38, c251] c1031 unsat1031 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1032 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨36, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c109, some c199, some c1031, some c281, some c72, some c158, some c197, some c194, some c154, some c141, some c271, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1032 : lratChecker f1032 p1032 = .success := by decide +kernel
theorem unsat1032 : Unsatisfiable (PosFin 57) f1032 := by
  apply lratCheckerSound f1032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1032
  · intro a ha; simp [p1032] at ha; subst a; trivial
  · exact checked1032
theorem derived1032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1032 := by
  apply localUnsat_implies_entails f1032 [c204, c109, c199, c1031, c281, c72, c158, c197, c194, c154, c141, c271] c1032 unsat1032 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c1031 := derived1031 a h
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1033 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨11, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c754, some c281, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1033 : lratChecker f1033 p1033 = .success := by decide +kernel
theorem unsat1033 : Unsatisfiable (PosFin 57) f1033 := by
  apply lratCheckerSound f1033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1033
  · intro a ha; simp [p1033] at ha; subst a; trivial
  · exact checked1033
theorem derived1033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1033 := by
  apply localUnsat_implies_entails f1033 [c158, c754, c281] c1033 unsat1033 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c754 := derived754 a h
  have h2 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1034 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c109, some c199, some c1032, some c1033, some c197, some c194, some c15, some c141, some c40, some c315, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1034 : lratChecker f1034 p1034 = .success := by decide +kernel
theorem unsat1034 : Unsatisfiable (PosFin 57) f1034 := by
  apply lratCheckerSound f1034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1034
  · intro a ha; simp [p1034] at ha; subst a; trivial
  · exact checked1034
theorem derived1034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1034 := by
  apply localUnsat_implies_entails f1034 [c204, c109, c199, c1032, c1033, c197, c194, c15, c141, c40, c315] c1034 unsat1034 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c1032 := derived1032 a h
  have h4 : Entails.eval a c1033 := derived1033 a h
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1035 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c1030, some c320, some c109, some c199, some c1027, some c1022, some c908, some c68, some c56, some c176, some c217, some c349, some c63, some c154, some c1, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1035 : lratChecker f1035 p1035 = .success := by decide +kernel
theorem unsat1035 : Unsatisfiable (PosFin 57) f1035 := by
  apply lratCheckerSound f1035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1035
  · intro a ha; simp [p1035] at ha; subst a; trivial
  · exact checked1035
theorem derived1035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1035 := by
  apply localUnsat_implies_entails f1035 [c983, c1030, c320, c109, c199, c1027, c1022, c908, c68, c56, c176, c217, c349, c63, c154, c1] c1035 unsat1035 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c1030 := derived1030 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c1027 := derived1027 a h
  have h6 : Entails.eval a c1022 := derived1022 a h
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c217 := h 216 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1036 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c199, some c204, some c1033, some c197, some c1034, some c194, some c701, some c386, some c252, some c141, some c702, some c211, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1036 : lratChecker f1036 p1036 = .success := by decide +kernel
theorem unsat1036 : Unsatisfiable (PosFin 57) f1036 := by
  apply lratCheckerSound f1036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1036
  · intro a ha; simp [p1036] at ha; subst a; trivial
  · exact checked1036
theorem derived1036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1036 := by
  apply localUnsat_implies_entails f1036 [c109, c199, c204, c1033, c197, c1034, c194, c701, c386, c252, c141, c702, c211] c1036 unsat1036 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1033 := derived1033 a h
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c1034 := derived1034 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c386 := h 385 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c702 := derived702 a h
  have h12 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1037 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c109, some c199, some c316, some c935, some c204, some c55, some c21, some c34, some c249, some c1036, some c187, some c159, some c252, some c340, some c211, some c65, some c284, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1037 : lratChecker f1037 p1037 = .success := by decide +kernel
theorem unsat1037 : Unsatisfiable (PosFin 57) f1037 := by
  apply lratCheckerSound f1037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1037
  · intro a ha; simp [p1037] at ha; subst a; trivial
  · exact checked1037
theorem derived1037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1037 := by
  apply localUnsat_implies_entails f1037 [c320, c109, c199, c316, c935, c204, c55, c21, c34, c249, c1036, c187, c159, c252, c340, c211, c65, c284] c1037 unsat1037 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c935 := derived935 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  have h10 : Entails.eval a c1036 := derived1036 a h
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c340 := h 339 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c65 := h 64 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1038 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c43, some c141, some c1, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1038 : lratChecker f1038 p1038 = .success := by decide +kernel
theorem unsat1038 : Unsatisfiable (PosFin 57) f1038 := by
  apply lratCheckerSound f1038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1038
  · intro a ha; simp [p1038] at ha; subst a; trivial
  · exact checked1038
theorem derived1038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1038 := by
  apply localUnsat_implies_entails f1038 [c43, c141, c1] c1038 unsat1038 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1039 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1030, some c320, some c204, some c1022, some c908, some c983, some c1011, some c1027, some c1035, some c1037, some c36, some c109, some c199, some c249, some c385, some c186, some c197, some c1038, some c315, some c211, some c49, some c252, some c24, some c187, some c914, some c194, some c271, some c154, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1039 : lratChecker f1039 p1039 = .success := by decide +kernel
theorem unsat1039 : Unsatisfiable (PosFin 57) f1039 := by
  apply lratCheckerSound f1039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1039
  · intro a ha; simp [p1039] at ha; subst a; trivial
  · exact checked1039
theorem derived1039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1039 := by
  apply localUnsat_implies_entails f1039 [c1030, c320, c204, c1022, c908, c983, c1011, c1027, c1035, c1037, c36, c109, c199, c249, c385, c186, c197, c1038, c315, c211, c49, c252, c24, c187, c914, c194, c271, c154] c1039 unsat1039 (by rfl) a
  have h0 : Entails.eval a c1030 := derived1030 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1022 := derived1022 a h
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c1011 := derived1011 a h
  have h7 : Entails.eval a c1027 := derived1027 a h
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c1037 := derived1037 a h
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c385 := h 384 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c1038 := derived1038 a h
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c211 := h 210 (by decide)
  have h20 : Entails.eval a c49 := h 48 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c24 := h 23 (by decide)
  have h23 : Entails.eval a c187 := h 186 (by decide)
  have h24 : Entails.eval a c914 := derived914 a h
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c271 := h 270 (by decide)
  have h27 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1040 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1022, some c908, some c983, some c1011, some c1027, some c1030, some c1035, some c1037, some c36, some c320, some c109, some c199, some c1039, some c134, some c304, some c197, some c387, some c158, some c186, some c345, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1040 : lratChecker f1040 p1040 = .success := by decide +kernel
theorem unsat1040 : Unsatisfiable (PosFin 57) f1040 := by
  apply lratCheckerSound f1040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1040
  · intro a ha; simp [p1040] at ha; subst a; trivial
  · exact checked1040
theorem derived1040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1040 := by
  apply localUnsat_implies_entails f1040 [c1022, c908, c983, c1011, c1027, c1030, c1035, c1037, c36, c320, c109, c199, c1039, c134, c304, c197, c387, c158, c186, c345] c1040 unsat1040 (by rfl) a
  have h0 : Entails.eval a c1022 := derived1022 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1011 := derived1011 a h
  have h4 : Entails.eval a c1027 := derived1027 a h
  have h5 : Entails.eval a c1030 := derived1030 a h
  have h6 : Entails.eval a c1035 := derived1035 a h
  have h7 : Entails.eval a c1037 := derived1037 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c1039 := derived1039 a h
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c304 := h 303 (by decide)
  have h15 : Entails.eval a c197 := h 196 (by decide)
  have h16 : Entails.eval a c387 := h 386 (by decide)
  have h17 : Entails.eval a c158 := h 157 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1041 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨36, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c158, some c345, some c186, some c138, some c387, some c384, some c318, some c311, some c49, some c701, some c96, some c89, some c102, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1041 : lratChecker f1041 p1041 = .success := by decide +kernel
theorem unsat1041 : Unsatisfiable (PosFin 57) f1041 := by
  apply lratCheckerSound f1041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1041
  · intro a ha; simp [p1041] at ha; subst a; trivial
  · exact checked1041
theorem derived1041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1041 := by
  apply localUnsat_implies_entails f1041 [c36, c158, c345, c186, c138, c387, c384, c318, c311, c49, c701, c96, c89, c102] c1041 unsat1041 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c701 := derived701 a h
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1042 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c310, some c318, some c49, some c311, some c701, some c96, some c89, some c102, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1042 : lratChecker f1042 p1042 = .success := by decide +kernel
theorem unsat1042 : Unsatisfiable (PosFin 57) f1042 := by
  apply lratCheckerSound f1042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1042
  · intro a ha; simp [p1042] at ha; subst a; trivial
  · exact checked1042
theorem derived1042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1042 := by
  apply localUnsat_implies_entails f1042 [c310, c318, c49, c311, c701, c96, c89, c102] c1042 unsat1042 (by rfl) a
  have h0 : Entails.eval a c310 := h 309 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1043 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c382, some c185, some c181, some c193, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1043 : lratChecker f1043 p1043 = .success := by decide +kernel
theorem unsat1043 : Unsatisfiable (PosFin 57) f1043 := by
  apply lratCheckerSound f1043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1043
  · intro a ha; simp [p1043] at ha; subst a; trivial
  · exact checked1043
theorem derived1043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1043 := by
  apply localUnsat_implies_entails f1043 [c701, c382, c185, c181, c193] c1043 unsat1043 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1044 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c908, some c1022, some c1027, some c1030, some c320, some c109, some c199, some c1035, some c1011, some c1037, some c1040, some c1041, some c197, some c36, some c387, some c253, some c1042, some c1043, some c311, some c315, some c318, some c43, some c203, some c210, some c1, some c246, some c181, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1044 : lratChecker f1044 p1044 = .success := by decide +kernel
theorem unsat1044 : Unsatisfiable (PosFin 57) f1044 := by
  apply lratCheckerSound f1044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1044
  · intro a ha; simp [p1044] at ha; subst a; trivial
  · exact checked1044
theorem derived1044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1044 := by
  apply localUnsat_implies_entails f1044 [c983, c908, c1022, c1027, c1030, c320, c109, c199, c1035, c1011, c1037, c1040, c1041, c197, c36, c387, c253, c1042, c1043, c311, c315, c318, c43, c203, c210, c1, c246, c181] c1044 unsat1044 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1022 := derived1022 a h
  have h3 : Entails.eval a c1027 := derived1027 a h
  have h4 : Entails.eval a c1030 := derived1030 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c1011 := derived1011 a h
  have h10 : Entails.eval a c1037 := derived1037 a h
  have h11 : Entails.eval a c1040 := derived1040 a h
  have h12 : Entails.eval a c1041 := derived1041 a h
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c387 := h 386 (by decide)
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c1042 := derived1042 a h
  have h18 : Entails.eval a c1043 := derived1043 a h
  have h19 : Entails.eval a c311 := h 310 (by decide)
  have h20 : Entails.eval a c315 := h 314 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c210 := h 209 (by decide)
  have h25 : Entails.eval a c1 := h 0 (by decide)
  have h26 : Entails.eval a c246 := h 245 (by decide)
  have h27 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1045 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨54, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c318, some c105, some c210, some c246, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1045 : lratChecker f1045 p1045 = .success := by decide +kernel
theorem unsat1045 : Unsatisfiable (PosFin 57) f1045 := by
  apply lratCheckerSound f1045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1045
  · intro a ha; simp [p1045] at ha; subst a; trivial
  · exact checked1045
theorem derived1045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1045 := by
  apply localUnsat_implies_entails f1045 [c315, c318, c105, c210, c246] c1045 unsat1045 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1046 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨36, by decide⟩, false), (⟨11, by decide⟩, true), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1041, some c36, some c109, some c345, some c1043, some c187, some c194, some c405, some c1045, some c211, some c49, some c311, some c15, some c344, some c381, some c66, some c230, some c89, some c21, some c262, some c533, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1046 : lratChecker f1046 p1046 = .success := by decide +kernel
theorem unsat1046 : Unsatisfiable (PosFin 57) f1046 := by
  apply lratCheckerSound f1046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1046
  · intro a ha; simp [p1046] at ha; subst a; trivial
  · exact checked1046
theorem derived1046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1046 := by
  apply localUnsat_implies_entails f1046 [c1041, c36, c109, c345, c1043, c187, c194, c405, c1045, c211, c49, c311, c15, c344, c381, c66, c230, c89, c21, c262, c533] c1046 unsat1046 (by rfl) a
  have h0 : Entails.eval a c1041 := derived1041 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c1043 := derived1043 a h
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c405 := derived405 a h
  have h8 : Entails.eval a c1045 := derived1045 a h
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c381 := h 380 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c89 := h 88 (by decide)
  have h18 : Entails.eval a c21 := h 20 (by decide)
  have h19 : Entails.eval a c262 := h 261 (by decide)
  have h20 : Entails.eval a c533 := derived533 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1047 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c908, some c1022, some c1027, some c1030, some c320, some c109, some c199, some c1035, some c1011, some c1037, some c1040, some c1041, some c197, some c36, some c1044, some c1046, some c1042, some c344, some c217, some c176, some c80, some c370, some c178, some c185, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1047 : lratChecker f1047 p1047 = .success := by decide +kernel
theorem unsat1047 : Unsatisfiable (PosFin 57) f1047 := by
  apply lratCheckerSound f1047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1047
  · intro a ha; simp [p1047] at ha; subst a; trivial
  · exact checked1047
theorem derived1047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1047 := by
  apply localUnsat_implies_entails f1047 [c983, c908, c1022, c1027, c1030, c320, c109, c199, c1035, c1011, c1037, c1040, c1041, c197, c36, c1044, c1046, c1042, c344, c217, c176, c80, c370, c178, c185] c1047 unsat1047 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1022 := derived1022 a h
  have h3 : Entails.eval a c1027 := derived1027 a h
  have h4 : Entails.eval a c1030 := derived1030 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c1011 := derived1011 a h
  have h10 : Entails.eval a c1037 := derived1037 a h
  have h11 : Entails.eval a c1040 := derived1040 a h
  have h12 : Entails.eval a c1041 := derived1041 a h
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c1044 := derived1044 a h
  have h16 : Entails.eval a c1046 := derived1046 a h
  have h17 : Entails.eval a c1042 := derived1042 a h
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c217 := h 216 (by decide)
  have h20 : Entails.eval a c176 := h 175 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c370 := h 369 (by decide)
  have h23 : Entails.eval a c178 := h 177 (by decide)
  have h24 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1048 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨34, by decide⟩, true), (⟨26, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c109, some c199, some c1037, some c1041, some c197, some c114, some c36, some c344, some c217, some c176, some c80, some c295, some c370, some c178, some c373, some c55, some c96, some c157, some c322, some c75, some c21, some c351, some c98, some c54, some c327, some c49, some c292, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1048 : lratChecker f1048 p1048 = .success := by decide +kernel
theorem unsat1048 : Unsatisfiable (PosFin 57) f1048 := by
  apply lratCheckerSound f1048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1048
  · intro a ha; simp [p1048] at ha; subst a; trivial
  · exact checked1048
theorem derived1048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1048 := by
  apply localUnsat_implies_entails f1048 [c320, c109, c199, c1037, c1041, c197, c114, c36, c344, c217, c176, c80, c295, c370, c178, c373, c55, c96, c157, c322, c75, c21, c351, c98, c54, c327, c49, c292] c1048 unsat1048 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1041 := derived1041 a h
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  have h19 : Entails.eval a c322 := h 321 (by decide)
  have h20 : Entails.eval a c75 := h 74 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c351 := h 350 (by decide)
  have h23 : Entails.eval a c98 := h 97 (by decide)
  have h24 : Entails.eval a c54 := h 53 (by decide)
  have h25 : Entails.eval a c327 := h 326 (by decide)
  have h26 : Entails.eval a c49 := h 48 (by decide)
  have h27 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1049 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1030, some c320, some c1027, some c1022, some c1011, some c983, some c908, some c109, some c199, some c1035, some c1037, some c36, some c1040, some c1041, some c197, some c1047, some c338, some c385, some c114, some c1048, some c310, some c318, some c211, some c311, some c252, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1049 : lratChecker f1049 p1049 = .success := by decide +kernel
theorem unsat1049 : Unsatisfiable (PosFin 57) f1049 := by
  apply lratCheckerSound f1049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1049
  · intro a ha; simp [p1049] at ha; subst a; trivial
  · exact checked1049
theorem derived1049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1049 := by
  apply localUnsat_implies_entails f1049 [c1030, c320, c1027, c1022, c1011, c983, c908, c109, c199, c1035, c1037, c36, c1040, c1041, c197, c1047, c338, c385, c114, c1048, c310, c318, c211, c311, c252] c1049 unsat1049 (by rfl) a
  have h0 : Entails.eval a c1030 := derived1030 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c1027 := derived1027 a h
  have h3 : Entails.eval a c1022 := derived1022 a h
  have h4 : Entails.eval a c1011 := derived1011 a h
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c1035 := derived1035 a h
  have h10 : Entails.eval a c1037 := derived1037 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c1040 := derived1040 a h
  have h13 : Entails.eval a c1041 := derived1041 a h
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c1047 := derived1047 a h
  have h16 : Entails.eval a c338 := h 337 (by decide)
  have h17 : Entails.eval a c385 := h 384 (by decide)
  have h18 : Entails.eval a c114 := h 113 (by decide)
  have h19 : Entails.eval a c1048 := derived1048 a h
  have h20 : Entails.eval a c310 := h 309 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c211 := h 210 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1050 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c186, some c90, some c177, some c23, some c244, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1050 : lratChecker f1050 p1050 = .success := by decide +kernel
theorem unsat1050 : Unsatisfiable (PosFin 57) f1050 := by
  apply lratCheckerSound f1050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1050
  · intro a ha; simp [p1050] at ha; subst a; trivial
  · exact checked1050
theorem derived1050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1050 := by
  apply localUnsat_implies_entails f1050 [c186, c90, c177, c23, c244] c1050 unsat1050 (by rfl) a
  have h0 : Entails.eval a c186 := h 185 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1051 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c983, some c1011, some c1022, some c1027, some c1030, some c1049, some c268, some c26, some c936, some c55, some c36, some c295, some c80, some c376, some c173, some c365, some c77, some c237, some c1050, some c369, some c84, some c244, some c23, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1051 : lratChecker f1051 p1051 = .success := by decide +kernel
theorem unsat1051 : Unsatisfiable (PosFin 57) f1051 := by
  apply lratCheckerSound f1051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1051
  · intro a ha; simp [p1051] at ha; subst a; trivial
  · exact checked1051
theorem derived1051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1051 := by
  apply localUnsat_implies_entails f1051 [c908, c983, c1011, c1022, c1027, c1030, c1049, c268, c26, c936, c55, c36, c295, c80, c376, c173, c365, c77, c237, c1050, c369, c84, c244, c23] c1051 unsat1051 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c1011 := derived1011 a h
  have h3 : Entails.eval a c1022 := derived1022 a h
  have h4 : Entails.eval a c1027 := derived1027 a h
  have h5 : Entails.eval a c1030 := derived1030 a h
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c936 := derived936 a h
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c365 := h 364 (by decide)
  have h17 : Entails.eval a c77 := h 76 (by decide)
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c1050 := derived1050 a h
  have h20 : Entails.eval a c369 := h 368 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c244 := h 243 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1052 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c35, some c385, some c908, some c56, some c80, some c341, some c345, some c55, some c66, some c367, some c89, some c102, some c47, some c81, some c300, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1052 : lratChecker f1052 p1052 = .success := by decide +kernel
theorem unsat1052 : Unsatisfiable (PosFin 57) f1052 := by
  apply lratCheckerSound f1052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1052
  · intro a ha; simp [p1052] at ha; subst a; trivial
  · exact checked1052
theorem derived1052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1052 := by
  apply localUnsat_implies_entails f1052 [c1051, c35, c385, c908, c56, c80, c341, c345, c55, c66, c367, c89, c102, c47, c81, c300] c1052 unsat1052 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1053 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c1051, some c908, some c35, some c1052, some c365, some c369, some c55, some c78, some c341, some c68, some c343, some c89, some c102, some c47, some c69, some c284, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1053 : lratChecker f1053 p1053 = .success := by decide +kernel
theorem unsat1053 : Unsatisfiable (PosFin 57) f1053 := by
  apply lratCheckerSound f1053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1053
  · intro a ha; simp [p1053] at ha; subst a; trivial
  · exact checked1053
theorem derived1053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1053 := by
  apply localUnsat_implies_entails f1053 [c385, c1051, c908, c35, c1052, c365, c369, c55, c78, c341, c68, c343, c89, c102, c47, c69, c284] c1053 unsat1053 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c1052 := derived1052 a h
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c102 := h 101 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1054 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨45, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨46, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c215, some c238, some c23, some c114, some c352, some c68, some c69, some c356, some c354, some c330, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1054 : lratChecker f1054 p1054 = .success := by decide +kernel
theorem unsat1054 : Unsatisfiable (PosFin 57) f1054 := by
  apply lratCheckerSound f1054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1054
  · intro a ha; simp [p1054] at ha; subst a; trivial
  · exact checked1054
theorem derived1054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1054 := by
  apply localUnsat_implies_entails f1054 [c102, c215, c238, c23, c114, c352, c68, c69, c356, c354, c330] c1054 unsat1054 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1055 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, true), (⟨53, by decide⟩, false), (⟨46, by decide⟩, true), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c345, some c344, some c330, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1055 : lratChecker f1055 p1055 = .success := by decide +kernel
theorem unsat1055 : Unsatisfiable (PosFin 57) f1055 := by
  apply lratCheckerSound f1055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1055
  · intro a ha; simp [p1055] at ha; subst a; trivial
  · exact checked1055
theorem derived1055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1055 := by
  apply localUnsat_implies_entails f1055 [c345, c344, c330] c1055 unsat1055 (by rfl) a
  have h0 : Entails.eval a c345 := h 344 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1056 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c1053, some c1051, some c26, some c107, some c10, some c385, some c908, some c5, some c184, some c256, some c387, some c368, some c1055, some c68, some c116, some c173, some c215, some c238, some c1054, some c356, some c58, some c84, some c156, some c354, some c229, some c331, some c259, some c300, some c307, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1056 : lratChecker f1056 p1056 = .success := by decide +kernel
theorem unsat1056 : Unsatisfiable (PosFin 57) f1056 := by
  apply lratCheckerSound f1056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1056
  · intro a ha; simp [p1056] at ha; subst a; trivial
  · exact checked1056
theorem derived1056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1056 := by
  apply localUnsat_implies_entails f1056 [c369, c1053, c1051, c26, c107, c10, c385, c908, c5, c184, c256, c387, c368, c1055, c68, c116, c173, c215, c238, c1054, c356, c58, c84, c156, c354, c229, c331, c259, c300, c307] c1056 unsat1056 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c1053 := derived1053 a h
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c1055 := derived1055 a h
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c215 := h 214 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  have h19 : Entails.eval a c1054 := derived1054 a h
  have h20 : Entails.eval a c356 := h 355 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  have h22 : Entails.eval a c84 := h 83 (by decide)
  have h23 : Entails.eval a c156 := h 155 (by decide)
  have h24 : Entails.eval a c354 := h 353 (by decide)
  have h25 : Entails.eval a c229 := h 228 (by decide)
  have h26 : Entails.eval a c331 := h 330 (by decide)
  have h27 : Entails.eval a c259 := h 258 (by decide)
  have h28 : Entails.eval a c300 := h 299 (by decide)
  have h29 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1057 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c387, some c381, some c307, some c302, some c315, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1057 : lratChecker f1057 p1057 = .success := by decide +kernel
theorem unsat1057 : Unsatisfiable (PosFin 57) f1057 := by
  apply lratCheckerSound f1057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1057
  · intro a ha; simp [p1057] at ha; subst a; trivial
  · exact checked1057
theorem derived1057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1057 := by
  apply localUnsat_implies_entails f1057 [c701, c387, c381, c307, c302, c315] c1057 unsat1057 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1058 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1053, some c1051, some c26, some c107, some c10, some c385, some c908, some c34, some c89, some c701, some c1057, some c137, some c184, some c191, some c313, some c198, some c202, some c17, some c43, some c33, some c317, some c246, some c110, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1058 : lratChecker f1058 p1058 = .success := by decide +kernel
theorem unsat1058 : Unsatisfiable (PosFin 57) f1058 := by
  apply lratCheckerSound f1058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1058
  · intro a ha; simp [p1058] at ha; subst a; trivial
  · exact checked1058
theorem derived1058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1058 := by
  apply localUnsat_implies_entails f1058 [c1053, c1051, c26, c107, c10, c385, c908, c34, c89, c701, c1057, c137, c184, c191, c313, c198, c202, c17, c43, c33, c317, c246, c110] c1058 unsat1058 (by rfl) a
  have h0 : Entails.eval a c1053 := derived1053 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c701 := derived701 a h
  have h10 : Entails.eval a c1057 := derived1057 a h
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c246 := h 245 (by decide)
  have h22 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1059 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c908, some c385, some c1053, some c26, some c107, some c10, some c1058, some c5, some c1056, some c184, some c56, some c80, some c1057, some c344, some c185, some c156, some c175, some c352, some c215, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1059 : lratChecker f1059 p1059 = .success := by decide +kernel
theorem unsat1059 : Unsatisfiable (PosFin 57) f1059 := by
  apply lratCheckerSound f1059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1059
  · intro a ha; simp [p1059] at ha; subst a; trivial
  · exact checked1059
theorem derived1059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1059 := by
  apply localUnsat_implies_entails f1059 [c1051, c908, c385, c1053, c26, c107, c10, c1058, c5, c1056, c184, c56, c80, c1057, c344, c185, c156, c175, c352, c215] c1059 unsat1059 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c1053 := derived1053 a h
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1058 := derived1058 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1056 := derived1056 a h
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c1057 := derived1057 a h
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1060 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c388, some c381, some c307, some c302, some c315, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1060 : lratChecker f1060 p1060 = .success := by decide +kernel
theorem unsat1060 : Unsatisfiable (PosFin 57) f1060 := by
  apply lratCheckerSound f1060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1060
  · intro a ha; simp [p1060] at ha; subst a; trivial
  · exact checked1060
theorem derived1060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1060 := by
  apply localUnsat_implies_entails f1060 [c701, c388, c381, c307, c302, c315] c1060 unsat1060 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1061 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c315, some c311, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1061 : lratChecker f1061 p1061 = .success := by decide +kernel
theorem unsat1061 : Unsatisfiable (PosFin 57) f1061 := by
  apply lratCheckerSound f1061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1061
  · intro a ha; simp [p1061] at ha; subst a; trivial
  · exact checked1061
theorem derived1061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1061 := by
  apply localUnsat_implies_entails f1061 [c313, c315, c311] c1061 unsat1061 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1062 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c105, some c1, some c4, some c191, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1062 : lratChecker f1062 p1062 = .success := by decide +kernel
theorem unsat1062 : Unsatisfiable (PosFin 57) f1062 := by
  apply lratCheckerSound f1062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1062
  · intro a ha; simp [p1062] at ha; subst a; trivial
  · exact checked1062
theorem derived1062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1062 := by
  apply localUnsat_implies_entails f1062 [c17, c105, c1, c4, c191] c1062 unsat1062 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1063 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c908, some c1059, some c92, some c36, some c701, some c93, some c1060, some c1061, some c1062, some c33, some c42, some c26, some c107, some c202, some c10, some c261, some c246, some c191, some c206, some c792, some c317, some c132, some c198, some c194, some c141, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1063 : lratChecker f1063 p1063 = .success := by decide +kernel
theorem unsat1063 : Unsatisfiable (PosFin 57) f1063 := by
  apply lratCheckerSound f1063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1063
  · intro a ha; simp [p1063] at ha; subst a; trivial
  · exact checked1063
theorem derived1063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1063 := by
  apply localUnsat_implies_entails f1063 [c1051, c908, c1059, c92, c36, c701, c93, c1060, c1061, c1062, c33, c42, c26, c107, c202, c10, c261, c246, c191, c206, c792, c317, c132, c198, c194, c141] c1063 unsat1063 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1059 := derived1059 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c1061 := derived1061 a h
  have h9 : Entails.eval a c1062 := derived1062 a h
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c246 := h 245 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c792 := derived792 a h
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c132 := h 131 (by decide)
  have h23 : Entails.eval a c198 := h 197 (by decide)
  have h24 : Entails.eval a c194 := h 193 (by decide)
  have h25 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1064 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c35, some c701, some c1061, some c42, some c17, some c1062, some c202, some c105, some c47, some c268, some c1, some c191, some c195, some c119, some c801, some c343, some c67, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1064 : lratChecker f1064 p1064 = .success := by decide +kernel
theorem unsat1064 : Unsatisfiable (PosFin 57) f1064 := by
  apply lratCheckerSound f1064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1064
  · intro a ha; simp [p1064] at ha; subst a; trivial
  · exact checked1064
theorem derived1064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1064 := by
  apply localUnsat_implies_entails f1064 [c1051, c35, c701, c1061, c42, c17, c1062, c202, c105, c47, c268, c1, c191, c195, c119, c801, c343, c67] c1064 unsat1064 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c1061 := derived1061 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1062 := derived1062 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c801 := derived801 a h
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1065 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c156, some c339, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1065 : lratChecker f1065 p1065 = .success := by decide +kernel
theorem unsat1065 : Unsatisfiable (PosFin 57) f1065 := by
  apply lratCheckerSound f1065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1065
  · intro a ha; simp [p1065] at ha; subst a; trivial
  · exact checked1065
theorem derived1065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1065 := by
  apply localUnsat_implies_entails f1065 [c184, c156, c339] c1065 unsat1065 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1066 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1063, some c28, some c103, some c1051, some c908, some c1061, some c42, some c17, some c1062, some c927, some c202, some c105, some c47, some c268, some c1, some c191, some c195, some c194, some c119, some c128, some c801, some c282, some c60, some c162, some c300, some c240, some c1065, some c6, some c170, some c77, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1066 : lratChecker f1066 p1066 = .success := by decide +kernel
theorem unsat1066 : Unsatisfiable (PosFin 57) f1066 := by
  apply lratCheckerSound f1066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1066
  · intro a ha; simp [p1066] at ha; subst a; trivial
  · exact checked1066
theorem derived1066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1066 := by
  apply localUnsat_implies_entails f1066 [c1063, c28, c103, c1051, c908, c1061, c42, c17, c1062, c927, c202, c105, c47, c268, c1, c191, c195, c194, c119, c128, c801, c282, c60, c162, c300, c240, c1065, c6, c170, c77] c1066 unsat1066 (by rfl) a
  have h0 : Entails.eval a c1063 := derived1063 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c1051 := derived1051 a h
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1061 := derived1061 a h
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1062 := derived1062 a h
  have h9 : Entails.eval a c927 := derived927 a h
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c191 := h 190 (by decide)
  have h16 : Entails.eval a c195 := h 194 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c128 := h 127 (by decide)
  have h20 : Entails.eval a c801 := derived801 a h
  have h21 : Entails.eval a c282 := h 281 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c162 := h 161 (by decide)
  have h24 : Entails.eval a c300 := h 299 (by decide)
  have h25 : Entails.eval a c240 := h 239 (by decide)
  have h26 : Entails.eval a c1065 := derived1065 a h
  have h27 : Entails.eval a c6 := h 5 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1067 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨30, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c184, some c313, some c6, some c301, some c108, some c317, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1067 : lratChecker f1067 p1067 = .success := by decide +kernel
theorem unsat1067 : Unsatisfiable (PosFin 57) f1067 := by
  apply lratCheckerSound f1067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1067
  · intro a ha; simp [p1067] at ha; subst a; trivial
  · exact checked1067
theorem derived1067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1067 := by
  apply localUnsat_implies_entails f1067 [c137, c184, c313, c6, c301, c108, c317] c1067 unsat1067 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1068 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1063, some c28, some c103, some c1051, some c908, some c1064, some c1066, some c386, some c382, some c89, some c101, some c46, some c1067, some c12, some c108, some c317, some c304, some c301, some c313, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1068 : lratChecker f1068 p1068 = .success := by decide +kernel
theorem unsat1068 : Unsatisfiable (PosFin 57) f1068 := by
  apply lratCheckerSound f1068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1068
  · intro a ha; simp [p1068] at ha; subst a; trivial
  · exact checked1068
theorem derived1068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1068 := by
  apply localUnsat_implies_entails f1068 [c1063, c28, c103, c1051, c908, c1064, c1066, c386, c382, c89, c101, c46, c1067, c12, c108, c317, c304, c301, c313] c1068 unsat1068 (by rfl) a
  have h0 : Entails.eval a c1063 := derived1063 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c1051 := derived1051 a h
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1064 := derived1064 a h
  have h6 : Entails.eval a c1066 := derived1066 a h
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c1067 := derived1067 a h
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c301 := h 300 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1069 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c200, some c188, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1069 : lratChecker f1069 p1069 = .success := by decide +kernel
theorem unsat1069 : Unsatisfiable (PosFin 57) f1069 := by
  apply lratCheckerSound f1069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1069
  · intro a ha; simp [p1069] at ha; subst a; trivial
  · exact checked1069
theorem derived1069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1069 := by
  apply localUnsat_implies_entails f1069 [c12, c200, c188] c1069 unsat1069 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1070 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c42, some c202, some c17, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1070 : lratChecker f1070 p1070 = .success := by decide +kernel
theorem unsat1070 : Unsatisfiable (PosFin 57) f1070 := by
  apply lratCheckerSound f1070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1070
  · intro a ha; simp [p1070] at ha; subst a; trivial
  · exact checked1070
theorem derived1070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1070 := by
  apply localUnsat_implies_entails f1070 [c1051, c42, c202, c17] c1070 unsat1070 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1071 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c195, some c123, some c183, some c245, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1071 : lratChecker f1071 p1071 = .success := by decide +kernel
theorem unsat1071 : Unsatisfiable (PosFin 57) f1071 := by
  apply lratCheckerSound f1071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1071
  · intro a ha; simp [p1071] at ha; subst a; trivial
  · exact checked1071
theorem derived1071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1071 := by
  apply localUnsat_implies_entails f1071 [c188, c195, c123, c183, c245] c1071 unsat1071 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c183 := h 182 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1072 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨19, by decide⟩, true), (⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c315, some c207, some c261, some c17, some c245, some c262, some c206, some c496, some c521, some c508, some c232, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1072 : lratChecker f1072 p1072 = .success := by decide +kernel
theorem unsat1072 : Unsatisfiable (PosFin 57) f1072 := by
  apply lratCheckerSound f1072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1072
  · intro a ha; simp [p1072] at ha; subst a; trivial
  · exact checked1072
theorem derived1072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1072 := by
  apply localUnsat_implies_entails f1072 [c1051, c315, c207, c261, c17, c245, c262, c206, c496, c521, c508, c232] c1072 unsat1072 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c496 := derived496 a h
  have h9 : Entails.eval a c521 := derived521 a h
  have h10 : Entails.eval a c508 := derived508 a h
  have h11 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1073 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c736, some c185, some c195, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1073 : lratChecker f1073 p1073 = .success := by decide +kernel
theorem unsat1073 : Unsatisfiable (PosFin 57) f1073 := by
  apply lratCheckerSound f1073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1073
  · intro a ha; simp [p1073] at ha; subst a; trivial
  · exact checked1073
theorem derived1073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1073 := by
  apply localUnsat_implies_entails f1073 [c736, c185, c195] c1073 unsat1073 (by rfl) a
  have h0 : Entails.eval a c736 := derived736 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1074 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c150, some c13, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1074 : lratChecker f1074 p1074 = .success := by decide +kernel
theorem unsat1074 : Unsatisfiable (PosFin 57) f1074 := by
  apply lratCheckerSound f1074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1074
  · intro a ha; simp [p1074] at ha; subst a; trivial
  · exact checked1074
theorem derived1074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1074 := by
  apply localUnsat_implies_entails f1074 [c46, c150, c13] c1074 unsat1074 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1075 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c1063, some c103, some c28, some c35, some c1068, some c387, some c388, some c254, some c107, some c1069, some c1070, some c313, some c315, some c151, some c1071, some c196, some c144, some c1074, some c317, some c309, some c386, some c382, some c1073, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1075 : lratChecker f1075 p1075 = .success := by decide +kernel
theorem unsat1075 : Unsatisfiable (PosFin 57) f1075 := by
  apply lratCheckerSound f1075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1075
  · intro a ha; simp [p1075] at ha; subst a; trivial
  · exact checked1075
theorem derived1075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1075 := by
  apply localUnsat_implies_entails f1075 [c1051, c1063, c103, c28, c35, c1068, c387, c388, c254, c107, c1069, c1070, c313, c315, c151, c1071, c196, c144, c1074, c317, c309, c386, c382, c1073] c1075 unsat1075 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1063 := derived1063 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c1068 := derived1068 a h
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c388 := h 387 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c1069 := derived1069 a h
  have h11 : Entails.eval a c1070 := derived1070 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c1071 := derived1071 a h
  have h16 : Entails.eval a c196 := h 195 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c1074 := derived1074 a h
  have h19 : Entails.eval a c317 := h 316 (by decide)
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c386 := h 385 (by decide)
  have h22 : Entails.eval a c382 := h 381 (by decide)
  have h23 : Entails.eval a c1073 := derived1073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1076 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c87, some c98, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1076 : lratChecker f1076 p1076 = .success := by decide +kernel
theorem unsat1076 : Unsatisfiable (PosFin 57) f1076 := by
  apply lratCheckerSound f1076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1076
  · intro a ha; simp [p1076] at ha; subst a; trivial
  · exact checked1076
theorem derived1076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1076 := by
  apply localUnsat_implies_entails f1076 [c93, c87, c98] c1076 unsat1076 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1077 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c23, some c114, some c274, some c276, some c69, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1077 : lratChecker f1077 p1077 = .success := by decide +kernel
theorem unsat1077 : Unsatisfiable (PosFin 57) f1077 := by
  apply lratCheckerSound f1077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1077
  · intro a ha; simp [p1077] at ha; subst a; trivial
  · exact checked1077
theorem derived1077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1077 := by
  apply localUnsat_implies_entails f1077 [c102, c23, c114, c274, c276, c69] c1077 unsat1077 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1078 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c276, some c69, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1078 : lratChecker f1078 p1078 = .success := by decide +kernel
theorem unsat1078 : Unsatisfiable (PosFin 57) f1078 := by
  apply lratCheckerSound f1078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1078
  · intro a ha; simp [p1078] at ha; subst a; trivial
  · exact checked1078
theorem derived1078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1078 := by
  apply localUnsat_implies_entails f1078 [c274, c276, c69] c1078 unsat1078 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1079 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1077, some c85, some c17, some c98, some c1078, some c156, some c65, some c798, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1079 : lratChecker f1079 p1079 = .success := by decide +kernel
theorem unsat1079 : Unsatisfiable (PosFin 57) f1079 := by
  apply lratCheckerSound f1079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1079
  · intro a ha; simp [p1079] at ha; subst a; trivial
  · exact checked1079
theorem derived1079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1079 := by
  apply localUnsat_implies_entails f1079 [c908, c1077, c85, c17, c98, c1078, c156, c65, c798] c1079 unsat1079 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1078 := derived1078 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c798 := derived798 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1080 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1075, some c39, some c701, some c1051, some c388, some c381, some c258, some c135, some c35, some c307, some c302, some c10, some c26, some c103, some c753, some c314, some c48, some c212, some c806, some c1076, some c385, some c256, some c1079, some c196, some c5, some c116, some c85, some c344, some c345, some c17, some c162, some c123, some c2, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1080 : lratChecker f1080 p1080 = .success := by decide +kernel
theorem unsat1080 : Unsatisfiable (PosFin 57) f1080 := by
  apply lratCheckerSound f1080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1080
  · intro a ha; simp [p1080] at ha; subst a; trivial
  · exact checked1080
theorem derived1080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1080 := by
  apply localUnsat_implies_entails f1080 [c908, c1075, c39, c701, c1051, c388, c381, c258, c135, c35, c307, c302, c10, c26, c103, c753, c314, c48, c212, c806, c1076, c385, c256, c1079, c196, c5, c116, c85, c344, c345, c17, c162, c123, c2] c1080 unsat1080 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1075 := derived1075 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c701 := derived701 a h
  have h4 : Entails.eval a c1051 := derived1051 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c753 := derived753 a h
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c212 := h 211 (by decide)
  have h19 : Entails.eval a c806 := derived806 a h
  have h20 : Entails.eval a c1076 := derived1076 a h
  have h21 : Entails.eval a c385 := h 384 (by decide)
  have h22 : Entails.eval a c256 := h 255 (by decide)
  have h23 : Entails.eval a c1079 := derived1079 a h
  have h24 : Entails.eval a c196 := h 195 (by decide)
  have h25 : Entails.eval a c5 := h 4 (by decide)
  have h26 : Entails.eval a c116 := h 115 (by decide)
  have h27 : Entails.eval a c85 := h 84 (by decide)
  have h28 : Entails.eval a c344 := h 343 (by decide)
  have h29 : Entails.eval a c345 := h 344 (by decide)
  have h30 : Entails.eval a c17 := h 16 (by decide)
  have h31 : Entails.eval a c162 := h 161 (by decide)
  have h32 : Entails.eval a c123 := h 122 (by decide)
  have h33 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1081 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1075, some c39, some c701, some c17, some c98, some c123, some c93, some c257, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1081 : lratChecker f1081 p1081 = .success := by decide +kernel
theorem unsat1081 : Unsatisfiable (PosFin 57) f1081 := by
  apply lratCheckerSound f1081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1081
  · intro a ha; simp [p1081] at ha; subst a; trivial
  · exact checked1081
theorem derived1081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1081 := by
  apply localUnsat_implies_entails f1081 [c908, c1075, c39, c701, c17, c98, c123, c93, c257] c1081 unsat1081 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1075 := derived1075 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c701 := derived701 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1082 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c257, some c85, some c123, some c246, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1082 : lratChecker f1082 p1082 = .success := by decide +kernel
theorem unsat1082 : Unsatisfiable (PosFin 57) f1082 := by
  apply lratCheckerSound f1082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1082
  · intro a ha; simp [p1082] at ha; subst a; trivial
  · exact checked1082
theorem derived1082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1082 := by
  apply localUnsat_implies_entails f1082 [c385, c257, c85, c123, c246] c1082 unsat1082 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1083 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1080, some c908, some c1075, some c39, some c701, some c1051, some c26, some c107, some c10, some c191, some c420, some c206, some c103, some c48, some c196, some c5, some c198, some c152, some c1081, some c1082, some c87, some c246, some c202, some c113, some c454, some c334, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1083 : lratChecker f1083 p1083 = .success := by decide +kernel
theorem unsat1083 : Unsatisfiable (PosFin 57) f1083 := by
  apply lratCheckerSound f1083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1083
  · intro a ha; simp [p1083] at ha; subst a; trivial
  · exact checked1083
theorem derived1083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1083 := by
  apply localUnsat_implies_entails f1083 [c1080, c908, c1075, c39, c701, c1051, c26, c107, c10, c191, c420, c206, c103, c48, c196, c5, c198, c152, c1081, c1082, c87, c246, c202, c113, c454, c334] c1083 unsat1083 (by rfl) a
  have h0 : Entails.eval a c1080 := derived1080 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1075 := derived1075 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c420 := derived420 a h
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c1081 := derived1081 a h
  have h19 : Entails.eval a c1082 := derived1082 a h
  have h20 : Entails.eval a c87 := h 86 (by decide)
  have h21 : Entails.eval a c246 := h 245 (by decide)
  have h22 : Entails.eval a c202 := h 201 (by decide)
  have h23 : Entails.eval a c113 := h 112 (by decide)
  have h24 : Entails.eval a c454 := derived454 a h
  have h25 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1084 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1080, some c908, some c1075, some c39, some c701, some c1051, some c26, some c107, some c10, some c191, some c103, some c206, some c420, some c1083, some c184, some c385, some c251, some c1076, some c121, some c246, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 57) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c1080, c908, c1075, c39, c701, c1051, c26, c107, c10, c191, c103, c206, c420, c1083, c184, c385, c251, c1076, c121, c246] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c1080 := derived1080 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1075 := derived1075 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c420 := derived420 a h
  have h13 : Entails.eval a c1083 := derived1083 a h
  have h14 : Entails.eval a c184 := h 183 (by decide)
  have h15 : Entails.eval a c385 := h 384 (by decide)
  have h16 : Entails.eval a c251 := h 250 (by decide)
  have h17 : Entails.eval a c1076 := derived1076 a h
  have h18 : Entails.eval a c121 := h 120 (by decide)
  have h19 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1080, some c908, some c1075, some c39, some c701, some c1051, some c26, some c107, some c10, some c191, some c103, some c48, some c1084, some c749, some c317, some c202, some c261, some c111, some c806, some c792, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c1080, c908, c1075, c39, c701, c1051, c26, c107, c10, c191, c103, c48, c1084, c749, c317, c202, c261, c111, c806, c792] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c1080 := derived1080 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1075 := derived1075 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c1084 := derived1084 a h
  have h13 : Entails.eval a c749 := derived749 a h
  have h14 : Entails.eval a c317 := h 316 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c806 := derived806 a h
  have h19 : Entails.eval a c792 := derived792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨31, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c261, some c111, some c141, some c195, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c202, c261, c111, c141, c195] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1080, some c908, some c1075, some c39, some c701, some c1051, some c26, some c103, some c107, some c48, some c10, some c191, some c1085, some c52, some c317, some c45, some c5, some c184, some c1086, some c106, some c753, some c791, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1080, c908, c1075, c39, c701, c1051, c26, c103, c107, c48, c10, c191, c1085, c52, c317, c45, c5, c184, c1086, c106, c753, c791] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1080 := derived1080 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1075 := derived1075 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c701 := derived701 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c1085 := derived1085 a h
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c1086 := derived1086 a h
  have h19 : Entails.eval a c106 := h 105 (by decide)
  have h20 : Entails.eval a c753 := derived753 a h
  have h21 : Entails.eval a c791 := derived791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c8, some c24, some c106, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c45, c8, c24, c106] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1088

end CochromaticTwenty.Certificates.B16_7_2
