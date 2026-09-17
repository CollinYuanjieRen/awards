import MerLeanExperiment.Certificates.B16_4_0.Steps0500_0599

/-! Generated from the actual pinned b16_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c957 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c99, some c101, some c871, some c148, some c3, some c193, some c60, some c150, some c292, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c702, c99, c101, c871, c148, c3, c193, c60, c150, c292] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c871 := derived871 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c150 := h 149 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c289, some c99, some c101, some c109, some c720, some c200, some c102, some c28, some c60, some c203, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c702, c289, c99, c101, c109, c720, c200, c102, c28, c60, c203] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c720 := derived720 a h
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c289, some c958, some c2, some c957, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c702, c289, c958, c2, c957] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c958 := derived958 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c957 := derived957 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c949, some c702, some c956, some c101, some c99, some c871, some c959, some c719, some c504, some c46, some c55, some c102, some c317, some c292, some c48, some c95, some c284, some c415, some c96, some c11, some c150, some c5, some c109, some c203, some c202, some c33, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c855, c949, c702, c956, c101, c99, c871, c959, c719, c504, c46, c55, c102, c317, c292, c48, c95, c284, c415, c96, c11, c150, c5, c109, c203, c202, c33] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c702 := derived702 a h
  have h3 : Entails.eval a c956 := derived956 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c871 := derived871 a h
  have h7 : Entails.eval a c959 := derived959 a h
  have h8 : Entails.eval a c719 := derived719 a h
  have h9 : Entails.eval a c504 := derived504 a h
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c415 := derived415 a h
  have h19 : Entails.eval a c96 := h 95 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c5 := h 4 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c202 := h 201 (by decide)
  have h26 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c949, some c702, some c956, some c334, some c335, some c960, some c18, some c907, some c65, some c15, some c107, some c104, some c11, some c140, some c155, some c113, some c871, some c872, some c294, some c207, some c148, some c28, some c522, some c255, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c855, c949, c702, c956, c334, c335, c960, c18, c907, c65, c15, c107, c104, c11, c140, c155, c113, c871, c872, c294, c207, c148, c28, c522, c255] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c702 := derived702 a h
  have h3 : Entails.eval a c956 := derived956 a h
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c960 := derived960 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c907 := derived907 a h
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c871 := derived871 a h
  have h18 : Entails.eval a c872 := derived872 a h
  have h19 : Entails.eval a c294 := h 293 (by decide)
  have h20 : Entails.eval a c207 := h 206 (by decide)
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c28 := h 27 (by decide)
  have h23 : Entails.eval a c522 := derived522 a h
  have h24 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c956, some c961, some c37, some c136, some c430, some c856, some c101, some c99, some c2, some c295, some c504, some c46, some c55, some c317, some c296, some c282, some c297, some c56, some c150, some c5, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c702, c855, c956, c961, c37, c136, c430, c856, c101, c99, c2, c295, c504, c46, c55, c317, c296, c282, c297, c56, c150, c5] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c956 := derived956 a h
  have h3 : Entails.eval a c961 := derived961 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c430 := derived430 a h
  have h7 : Entails.eval a c856 := derived856 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c504 := derived504 a h
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c317 := h 316 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c297 := h 296 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c949, some c702, some c855, some c956, some c335, some c962, some c136, some c37, some c2, some c138, some c888, some c160, some c15, some c22, some c429, some c99, some c101, some c856, some c504, some c46, some c55, some c296, some c209, some c262, some c28, some c823, some c243, some c279, some c286, some c97, some c352, some c297, some c287, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c949, c702, c855, c956, c335, c962, c136, c37, c2, c138, c888, c160, c15, c22, c429, c99, c101, c856, c504, c46, c55, c296, c209, c262, c28, c823, c243, c279, c286, c97, c352, c297, c287] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c949 := derived949 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c956 := derived956 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c962 := derived962 a h
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c888 := derived888 a h
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c429 := derived429 a h
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c856 := derived856 a h
  have h18 : Entails.eval a c504 := derived504 a h
  have h19 : Entails.eval a c46 := h 45 (by decide)
  have h20 : Entails.eval a c55 := h 54 (by decide)
  have h21 : Entails.eval a c296 := h 295 (by decide)
  have h22 : Entails.eval a c209 := h 208 (by decide)
  have h23 : Entails.eval a c262 := h 261 (by decide)
  have h24 : Entails.eval a c28 := h 27 (by decide)
  have h25 : Entails.eval a c823 := derived823 a h
  have h26 : Entails.eval a c243 := h 242 (by decide)
  have h27 : Entails.eval a c279 := h 278 (by decide)
  have h28 : Entails.eval a c286 := h 285 (by decide)
  have h29 : Entails.eval a c97 := h 96 (by decide)
  have h30 : Entails.eval a c352 := h 351 (by decide)
  have h31 : Entails.eval a c297 := h 296 (by decide)
  have h32 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c855, some c962, some c956, some c335, some c37, some c136, some c856, some c101, some c99, some c429, some c2, some c138, some c160, some c197, some c963, some c294, some c205, some c28, some c118, some c209, some c273, some c304, some c60, some c170, some c3, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c702, c949, c855, c962, c956, c335, c37, c136, c856, c101, c99, c429, c2, c138, c160, c197, c963, c294, c205, c28, c118, c209, c273, c304, c60, c170, c3] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c962 := derived962 a h
  have h4 : Entails.eval a c956 := derived956 a h
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c856 := derived856 a h
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c429 := derived429 a h
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c197 := h 196 (by decide)
  have h16 : Entails.eval a c963 := derived963 a h
  have h17 : Entails.eval a c294 := h 293 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c209 := h 208 (by decide)
  have h22 : Entails.eval a c273 := h 272 (by decide)
  have h23 : Entails.eval a c304 := h 303 (by decide)
  have h24 : Entails.eval a c60 := h 59 (by decide)
  have h25 : Entails.eval a c170 := h 169 (by decide)
  have h26 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c949, some c964, some c962, some c956, some c335, some c289, some c288, some c959, some c138, some c266, some c18, some c907, some c11, some c195, some c198, some c295, some c200, some c61, some c127, some c108, some c105, some c255, some c29, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c855, c702, c949, c964, c962, c956, c335, c289, c288, c959, c138, c266, c18, c907, c11, c195, c198, c295, c200, c61, c127, c108, c105, c255, c29] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c964 := derived964 a h
  have h4 : Entails.eval a c962 := derived962 a h
  have h5 : Entails.eval a c956 := derived956 a h
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c959 := derived959 a h
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c907 := derived907 a h
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c295 := h 294 (by decide)
  have h18 : Entails.eval a c200 := h 199 (by decide)
  have h19 : Entails.eval a c61 := h 60 (by decide)
  have h20 : Entails.eval a c127 := h 126 (by decide)
  have h21 : Entails.eval a c108 := h 107 (by decide)
  have h22 : Entails.eval a c105 := h 104 (by decide)
  have h23 : Entails.eval a c255 := h 254 (by decide)
  have h24 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c965, some c964, some c719, some c102, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 57) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c965, c964, c719, c102] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c965 := derived965 a h
  have h1 : Entails.eval a c964 := derived964 a h
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨28, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c949, some c965, some c964, some c962, some c956, some c504, some c48, some c966, some c18, some c907, some c895, some c108, some c195, some c198, some c56, some c146, some c292, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 57) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c855, c949, c965, c964, c962, c956, c504, c48, c966, c18, c907, c895, c108, c195, c198, c56, c146, c292] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c965 := derived965 a h
  have h3 : Entails.eval a c964 := derived964 a h
  have h4 : Entails.eval a c962 := derived962 a h
  have h5 : Entails.eval a c956 := derived956 a h
  have h6 : Entails.eval a c504 := derived504 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c966 := derived966 a h
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c907 := derived907 a h
  have h11 : Entails.eval a c895 := derived895 a h
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c968 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c965, some c964, some c962, some c956, some c967, some c99, some c18, some c907, some c895, some c105, some c195, some c897, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 57) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c702, c949, c965, c964, c962, c956, c967, c99, c18, c907, c895, c105, c195, c897] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c965 := derived965 a h
  have h3 : Entails.eval a c964 := derived964 a h
  have h4 : Entails.eval a c962 := derived962 a h
  have h5 : Entails.eval a c956 := derived956 a h
  have h6 : Entails.eval a c967 := derived967 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c907 := derived907 a h
  have h10 : Entails.eval a c895 := derived895 a h
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c897 := derived897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c949, some c702, some c965, some c964, some c962, some c956, some c335, some c18, some c907, some c895, some c11, some c65, some c899, some c883, some c155, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 57) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c855, c949, c702, c965, c964, c962, c956, c335, c18, c907, c895, c11, c65, c899, c883, c155] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c702 := derived702 a h
  have h3 : Entails.eval a c965 := derived965 a h
  have h4 : Entails.eval a c964 := derived964 a h
  have h5 : Entails.eval a c962 := derived962 a h
  have h6 : Entails.eval a c956 := derived956 a h
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c907 := derived907 a h
  have h10 : Entails.eval a c895 := derived895 a h
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c899 := derived899 a h
  have h14 : Entails.eval a c883 := derived883 a h
  have h15 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c949, some c962, some c964, some c965, some c968, some c291, some c969, some c101, some c99, some c966, some c871, some c504, some c95, some c138, some c11, some c96, some c183, some c415, some c284, some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 57) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c855, c702, c949, c962, c964, c965, c968, c291, c969, c101, c99, c966, c871, c504, c95, c138, c11, c96, c183, c415, c284] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c962 := derived962 a h
  have h4 : Entails.eval a c964 := derived964 a h
  have h5 : Entails.eval a c965 := derived965 a h
  have h6 : Entails.eval a c968 := derived968 a h
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c969 := derived969 a h
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c966 := derived966 a h
  have h12 : Entails.eval a c871 := derived871 a h
  have h13 : Entails.eval a c504 := derived504 a h
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c183 := h 182 (by decide)
  have h19 : Entails.eval a c415 := derived415 a h
  have h20 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c971 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c855, some c330, some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 57) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c970, c855, c330] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c972 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c855, some c332, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 57) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c970, c855, c332] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c972, some c702, some c971, some c855, some c970, some c38, some c137, some c264, some c104, some c99, some c6, some c291, some c292, some c263, some c331, some c914, some c111, some c895, some c61, some c601, some c594, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 57) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c972, c702, c971, c855, c970, c38, c137, c264, c104, c99, c6, c291, c292, c263, c331, c914, c111, c895, c61, c601, c594] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c855 := derived855 a h
  have h4 : Entails.eval a c970 := derived970 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  have h15 : Entails.eval a c914 := derived914 a h
  have h16 : Entails.eval a c111 := h 110 (by decide)
  have h17 : Entails.eval a c895 := derived895 a h
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c601 := derived601 a h
  have h20 : Entails.eval a c594 := derived594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c610, some c7, some c258, some c110, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 57) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c971, c610, c7, c258, c110] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c610 := derived610 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, true), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c27, some c974, some c19, some c66, some c725, some c258, some c726, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 57) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c971, c27, c974, c19, c66, c725, c258, c726] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c974 := derived974 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c725 := derived725 a h
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c971, some c949, some c973, some c288, some c138, some c331, some c289, some c148, some c27, some c975, some c61, some c295, some c208, some c149, some c110, some c197, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 57) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c970, c971, c949, c973, c288, c138, c331, c289, c148, c27, c975, c61, c295, c208, c149, c110, c197] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c973 := derived973 a h
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c975 := derived975 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c971, some c107, some c104, some c66, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 57) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c702, c971, c107, c104, c66] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c971, some c973, some c288, some c138, some c331, some c977, some c976, some c718, some c950, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 57) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c970, c971, c973, c288, c138, c331, c977, c976, c718, c950] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c977 := derived977 a h
  have h7 : Entails.eval a c976 := derived976 a h
  have h8 : Entails.eval a c718 := derived718 a h
  have h9 : Entails.eval a c950 := derived950 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c970, some c972, some c971, some c973, some c288, some c289, some c978, some c11, some c533, some c195, some c198, some c846, some c110, some c158, some c292, some c911, some c151, some c27, some c199, some c193, some c258, some c125, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 57) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c702, c949, c970, c972, c971, c973, c288, c289, c978, c11, c533, c195, c198, c846, c110, c158, c292, c911, c151, c27, c199, c193, c258, c125] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c970 := derived970 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c971 := derived971 a h
  have h5 : Entails.eval a c973 := derived973 a h
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c978 := derived978 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c533 := derived533 a h
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c198 := h 197 (by decide)
  have h13 : Entails.eval a c846 := derived846 a h
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c911 := derived911 a h
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  have h22 : Entails.eval a c258 := h 257 (by decide)
  have h23 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c971, some c979, some c717, some c916, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 57) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c970, c971, c979, c717, c916] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c979 := derived979 a h
  have h3 : Entails.eval a c717 := derived717 a h
  have h4 : Entails.eval a c916 := derived916 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c972, some c855, some c970, some c980, some c971, some c195, some c158, some c2, some c198, some c409, some c99, some c117, some c300, some c301, some c172, some c199, some c144, some c125, some c627, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 57) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c702, c949, c972, c855, c970, c980, c971, c195, c158, c2, c198, c409, c99, c117, c300, c301, c172, c199, c144, c125, c627] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c972 := derived972 a h
  have h3 : Entails.eval a c855 := derived855 a h
  have h4 : Entails.eval a c970 := derived970 a h
  have h5 : Entails.eval a c980 := derived980 a h
  have h6 : Entails.eval a c971 := derived971 a h
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c409 := derived409 a h
  have h12 : Entails.eval a c99 := h 98 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c301 := h 300 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c627 := derived627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c702, some c971, some c972, some c99, some c67, some c102, some c19, some c717, some c101, some c251, some c252, some c223, some c33, some c255, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 57) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c970, c702, c971, c972, c99, c67, c102, c19, c717, c101, c251, c252, c223, c33, c255] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c717 := derived717 a h
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c970, some c971, some c99, some c717, some c982, some c981, some c138, some c111, some c577, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 57) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c702, c970, c971, c99, c717, c982, c981, c138, c111, c577] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c970 := derived970 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c717 := derived717 a h
  have h5 : Entails.eval a c982 := derived982 a h
  have h6 : Entails.eval a c981 := derived981 a h
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c577 := derived577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c984 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c980, some c45, some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 57) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c983, c980, c45] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c980 := derived980 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c984, some c971, some c980, some c983, some c331, some c932, some c313, some c977, some c930, some c54, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 57) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c970, c984, c971, c980, c983, c331, c932, c313, c977, c930, c54] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c984 := derived984 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c980 := derived980 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c932 := derived932 a h
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c977 := derived977 a h
  have h9 : Entails.eval a c930 := derived930 a h
  have h10 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c702, some c949, some c983, some c855, some c970, some c980, some c985, some c138, some c111, some c577, some c593, some c104, some c197, some c54, some c888, some c144, some c160, some c293, some c497, some c921, some c297, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 57) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c971, c702, c949, c983, c855, c970, c980, c985, c138, c111, c577, c593, c104, c197, c54, c888, c144, c160, c293, c497, c921, c297] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c970 := derived970 a h
  have h6 : Entails.eval a c980 := derived980 a h
  have h7 : Entails.eval a c985 := derived985 a h
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c577 := derived577 a h
  have h11 : Entails.eval a c593 := derived593 a h
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c888 := derived888 a h
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c497 := derived497 a h
  have h20 : Entails.eval a c921 := derived921 a h
  have h21 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c987 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c702, some c949, some c11, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 57) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c986, c702, c949, c11] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c949, some c195, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 57) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c986, c949, c195] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c949, some c198, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c986, c949, c198] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c987, some c983, some c980, some c54, some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 57) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c987, c983, c980, c54] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c987 := derived987 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c980 := derived980 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c988, some c971, some c137, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 57) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c988, c971, c137] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c988 := derived988 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c988, some c971, some c110, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 57) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c988, c971, c110] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c988 := derived988 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c988, some c971, some c972, some c158, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 57) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c988, c971, c972, c158] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c988 := derived988 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c972 := derived972 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c990, some c991, some c992, some c208, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c990, c991, c992, c208] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c990 := derived990 a h
  have h1 : Entails.eval a c991 := derived991 a h
  have h2 : Entails.eval a c992 := derived992 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c991, some c990, some c295, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c991, c990, c295] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c991 := derived991 a h
  have h1 : Entails.eval a c990 := derived990 a h
  have h2 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c992, some c987, some c983, some c725, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c992, c987, c983, c725] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c992 := derived992 a h
  have h1 : Entails.eval a c987 := derived987 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c725 := derived725 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c997 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c994, some c987, some c983, some c27, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 57) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c994, c987, c983, c27] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c994 := derived994 a h
  have h1 : Entails.eval a c987 := derived987 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c995, some c983, some c980, some c53, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 57) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c995, c983, c980, c53] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c995 := derived995 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c980 := derived980 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c996, some c985, some c972, some c223, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c996, c985, c972, c223] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c996 := derived996 a h
  have h1 : Entails.eval a c985 := derived985 a h
  have h2 : Entails.eval a c972 := derived972 a h
  have h3 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c992, some c252, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c997, c992, c252] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c992 := derived992 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c997, some c999, some c255, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c997, c999, c255] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c997 := derived997 a h
  have h1 : Entails.eval a c999 := derived999 a h
  have h2 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1000, some c987, some c994, some c34, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c1000, c987, c994, c34] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c1000 := derived1000 a h
  have h1 : Entails.eval a c987 := derived987 a h
  have h2 : Entails.eval a c994 := derived994 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1000, some c989, some c1001, some c132, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c1000, c989, c1001, c132] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c1000 := derived1000 a h
  have h1 : Entails.eval a c989 := derived989 a h
  have h2 : Entails.eval a c1001 := derived1001 a h
  have h3 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1002, some c1003, some c993, some c13, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c1002, c1003, c993, c13] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c1002 := derived1002 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1002, some c998, some c105, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c1002, c998, c105] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c1002 := derived1002 a h
  have h1 : Entails.eval a c998 := derived998 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1004, some c1005, some c971, some c972, some c67]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c1004, c1005, c971, c972, c67] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c1004 := derived1004 a h
  have h1 : Entails.eval a c1005 := derived1005 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c972 := derived972 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1006

end CochromaticTwenty.Certificates.B16_4_0
