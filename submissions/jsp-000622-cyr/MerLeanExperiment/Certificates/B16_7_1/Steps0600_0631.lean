import MerLeanExperiment.Certificates.B16_7_1.Steps0500_0599

/-! Generated from the actual pinned b16_7_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c958 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c920, some c953, some c178, some c176, some c956, some c957, some c955, some c784, some c654, some c352, some c656, some c513, some c910, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c783, c920, c953, c178, c176, c956, c957, c955, c784, c654, c352, c656, c513, c910] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c953 := derived953 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c956 := derived956 a h
  have h6 : Entails.eval a c957 := derived957 a h
  have h7 : Entails.eval a c955 := derived955 a h
  have h8 : Entails.eval a c784 := derived784 a h
  have h9 : Entails.eval a c654 := derived654 a h
  have h10 : Entails.eval a c352 := h 351 (by decide)
  have h11 : Entails.eval a c656 := derived656 a h
  have h12 : Entails.eval a c513 := derived513 a h
  have h13 : Entails.eval a c910 := derived910 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c920, some c958, some c117, some c107, some c99, some c910, some c290, some c251, some c656, some c650, some c352, some c178, some c654, some c116, some c256, some c241, some c247, some c205, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c878, c783, c920, c958, c117, c107, c99, c910, c290, c251, c656, c650, c352, c178, c654, c116, c256, c241, c247, c205] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c958 := derived958 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c910 := derived910 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  have h10 : Entails.eval a c656 := derived656 a h
  have h11 : Entails.eval a c650 := derived650 a h
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c654 := derived654 a h
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c241 := h 240 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c958, some c959, some c117, some c99, some c295, some c294, some c188, some c194, some c243, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c878, c958, c959, c117, c99, c295, c294, c188, c194, c243] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c958 := derived958 a h
  have h2 : Entails.eval a c959 := derived959 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨21, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c878, some c920, some c960, some c959, some c117, some c107, some c99, some c241, some c116, some c178, some c650, some c652, some c299, some c263, some c223, some c101, some c149, some c279, some c410, some c313, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c958, c878, c920, c960, c959, c117, c107, c99, c241, c116, c178, c650, c652, c299, c263, c223, c101, c149, c279, c410, c313] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c960 := derived960 a h
  have h4 : Entails.eval a c959 := derived959 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c650 := derived650 a h
  have h12 : Entails.eval a c652 := derived652 a h
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c279 := h 278 (by decide)
  have h19 : Entails.eval a c410 := derived410 a h
  have h20 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c958, some c920, some c959, some c117, some c99, some c960, some c961, some c188, some c187, some c299, some c247, some c650, some c116, some c178, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c878, c958, c920, c959, c117, c99, c960, c961, c188, c187, c299, c247, c650, c116, c178] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c958 := derived958 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c959 := derived959 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c960 := derived960 a h
  have h7 : Entails.eval a c961 := derived961 a h
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c650 := derived650 a h
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c920, some c878, some c783, some c962, some c959, some c117, some c99, some c187, some c246, some c248, some c786, some c662, some c178, some c103, some c652, some c229, some c651, some c38, some c279, some c10, some c346, some c43, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c958, c920, c878, c783, c962, c959, c117, c99, c187, c246, c248, c786, c662, c178, c103, c652, c229, c651, c38, c279, c10, c346, c43] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c962 := derived962 a h
  have h5 : Entails.eval a c959 := derived959 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c786 := derived786 a h
  have h12 : Entails.eval a c662 := derived662 a h
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c652 := derived652 a h
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c651 := derived651 a h
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c279 := h 278 (by decide)
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c346 := h 345 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c920, some c878, some c783, some c959, some c117, some c99, some c963, some c241, some c116, some c178, some c650, some c652, some c299, some c223, some c280, some c279, some c351, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c958, c920, c878, c783, c959, c117, c99, c963, c241, c116, c178, c650, c652, c299, c223, c280, c279, c351] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c783 := derived783 a h
  have h4 : Entails.eval a c959 := derived959 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c963 := derived963 a h
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c650 := derived650 a h
  have h12 : Entails.eval a c652 := derived652 a h
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c878, some c958, some c99, some c964, some c294, some c295, some c959, some c117, some c243, some c241, some c893, some c116, some c192, some c280, some c178, some c297, some c351, some c137, some c651, some c896, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c920, c783, c878, c958, c99, c964, c294, c295, c959, c117, c243, c241, c893, c116, c192, c280, c178, c297, c351, c137, c651, c896] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c958 := derived958 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c964 := derived964 a h
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c959 := derived959 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c893 := derived893 a h
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c178 := h 177 (by decide)
  have h17 : Entails.eval a c297 := h 296 (by decide)
  have h18 : Entails.eval a c351 := h 350 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c651 := derived651 a h
  have h21 : Entails.eval a c896 := derived896 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c920, some c878, some c965, some c107, some c99, some c964, some c256, some c294, some c295, some c962, some c117, some c178, some c650, some c263, some c112, some c410, some c250, some c138, some c137, some c944, some c297, some c248, some c192, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 57) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c958, c920, c878, c965, c107, c99, c964, c256, c294, c295, c962, c117, c178, c650, c263, c112, c410, c250, c138, c137, c944, c297, c248, c192] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c965 := derived965 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c964 := derived964 a h
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c962 := derived962 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c650 := derived650 a h
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c410 := derived410 a h
  have h17 : Entails.eval a c250 := h 249 (by decide)
  have h18 : Entails.eval a c138 := h 137 (by decide)
  have h19 : Entails.eval a c137 := h 136 (by decide)
  have h20 : Entails.eval a c944 := derived944 a h
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c248 := h 247 (by decide)
  have h23 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c99, some c107, some c962, some c964, some c256, some c965, some c966, some c116, some c786, some c250, some c205, some c207, some c322, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 57) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c958, c99, c107, c962, c964, c256, c965, c966, c116, c786, c250, c205, c207, c322] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c962 := derived962 a h
  have h4 : Entails.eval a c964 := derived964 a h
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c965 := derived965 a h
  have h7 : Entails.eval a c966 := derived966 a h
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c786 := derived786 a h
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c968 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c967, some c920, some c176, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 57) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c967, c920, c176] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c967 := derived967 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c967, some c920, some c175, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 57) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c967, c920, c175] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c967 := derived967 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c968, some c650, some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 57) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c968, c650] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c650 := derived650 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c971 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c968, some c878, some c652, some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 57) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c968, c878, c652] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c652 := derived652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c972 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c969, some c968, some c653, some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 57) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c969, c968, c653] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c969 := derived969 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c653 := derived653 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c783, some c346, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 57) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c972, c783, c346] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c783, some c352, some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 57) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c972, c783, c352] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c974, some c968, some c651, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 57) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c974, c968, c651] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c974 := derived974 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c651 := derived651 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c975, some c967, some c180, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 57) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c975, c967, c180] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c975 := derived975 a h
  have h1 : Entails.eval a c967 := derived967 a h
  have h2 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c968, some c969, some c878, some c976, some c958, some c103, some c122, some c120, some c295, some c298, some c250, some c137, some c190, some c296, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 57) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c968, c969, c878, c976, c958, c103, c122, c120, c295, c298, c250, c137, c190, c296] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c968 := derived968 a h
  have h1 : Entails.eval a c969 := derived969 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c976 := derived976 a h
  have h4 : Entails.eval a c958 := derived958 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c971, some c968, some c878, some c969, some c976, some c958, some c970, some c977, some c238, some c102, some c119, some c121, some c298, some c297, some c250, some c138, some c190, some c299, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 57) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c972, c971, c968, c878, c969, c976, c958, c970, c977, c238, c102, c119, c121, c298, c297, c250, c138, c190, c299] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c968 := derived968 a h
  have h3 : Entails.eval a c878 := derived878 a h
  have h4 : Entails.eval a c969 := derived969 a h
  have h5 : Entails.eval a c976 := derived976 a h
  have h6 : Entails.eval a c958 := derived958 a h
  have h7 : Entails.eval a c970 := derived970 a h
  have h8 : Entails.eval a c977 := derived977 a h
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c297 := h 296 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c138 := h 137 (by decide)
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c978, some c974, some c967, some c674, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 57) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c978, c974, c967, c674] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c978 := derived978 a h
  have h1 : Entails.eval a c974 := derived974 a h
  have h2 : Entails.eval a c967 := derived967 a h
  have h3 : Entails.eval a c674 := derived674 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c978, some c974, some c973, some c279, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 57) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c978, c974, c973, c279] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c978 := derived978 a h
  have h1 : Entails.eval a c974 := derived974 a h
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c978, some c974, some c38, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 57) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c978, c974, c38] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c978 := derived978 a h
  have h1 : Entails.eval a c974 := derived974 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c980, some c970, some c290, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 57) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c980, c970, c290] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c980 := derived980 a h
  have h1 : Entails.eval a c970 := derived970 a h
  have h2 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c980, some c970, some c292, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 57) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c980, c970, c292] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c980 := derived980 a h
  have h1 : Entails.eval a c970 := derived970 a h
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c984 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c979, some c982, some c48, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 57) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c983, c979, c982, c48] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c979 := derived979 a h
  have h2 : Entails.eval a c982 := derived982 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c984, some c981, some c93, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 57) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c984, c981, c93] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c984 := derived984 a h
  have h1 : Entails.eval a c981 := derived981 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c984, some c981, some c975, some c7, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 57) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c984, c981, c975, c7] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c984 := derived984 a h
  have h1 : Entails.eval a c981 := derived981 a h
  have h2 : Entails.eval a c975 := derived975 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c987 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c985, some c982, some c979, some c49, some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 57) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c985, c982, c979, c49] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c985 := derived985 a h
  have h1 : Entails.eval a c982 := derived982 a h
  have h2 : Entails.eval a c979 := derived979 a h
  have h3 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c969, some c983, some c136, some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 57) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c986, c969, c983, c136] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c969 := derived969 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c988, some c987, some c980, some c293]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c988, c987, c980, c293] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c988 := derived988 a h
  have h1 : Entails.eval a c987 := derived987 a h
  have h2 : Entails.eval a c980 := derived980 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived989

end CochromaticTwenty.Certificates.B16_7_1
