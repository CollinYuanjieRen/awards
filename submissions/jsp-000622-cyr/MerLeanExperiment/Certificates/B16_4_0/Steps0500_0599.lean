import MerLeanExperiment.Certificates.B16_4_0.Steps0400_0499

/-! Generated from the actual pinned b16_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c857 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨34, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c410, some c104, some c107, some c37, some c45, some c333, some c314, some c315, some c67, some c95, some c108, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c702, c855, c410, c104, c107, c37, c45, c333, c314, c315, c67, c95, c108] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c410 := derived410 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c104, some c857, some c2, some c429, some c138, some c577, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c702, c104, c857, c2, c429, c138, c577] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c429 := derived429 a h
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c577 := derived577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨48, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c84, some c104, some c107, some c50, some c90, some c209, some c349, some c23, some c28, some c342, some c311, some c243, some c235, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c702, c84, c104, c107, c50, c90, c209, c349, c23, c28, c342, c311, c243, c235] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨55, by decide⟩, true), (⟨54, by decide⟩, false), (⟨42, by decide⟩, true), (⟨48, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c328, some c168, some c122, some c287, some c191, some c209, some c297, some c151, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c311, c328, c168, c122, c287, c191, c209, c297, c151] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c23, some c209, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c42, c23, c209] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨38, by decide⟩, false), (⟨42, by decide⟩, true), (⟨48, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c279, some c352, some c178, some c860, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c328, c279, c352, c178, c860] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c352 := h 351 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c860 := derived860 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c104, some c107, some c143, some c145, some c858, some c330, some c856, some c37, some c2, some c429, some c138, some c721, some c124, some c86, some c306, some c861, some c862, some c90, some c859, some c320, some c279, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c855, c702, c104, c107, c143, c145, c858, c330, c856, c37, c2, c429, c138, c721, c124, c86, c306, c861, c862, c90, c859, c320, c279] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c858 := derived858 a h
  have h7 : Entails.eval a c330 := h 329 (by decide)
  have h8 : Entails.eval a c856 := derived856 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c429 := derived429 a h
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c721 := derived721 a h
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c306 := h 305 (by decide)
  have h17 : Entails.eval a c861 := derived861 a h
  have h18 : Entails.eval a c862 := derived862 a h
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c859 := derived859 a h
  have h21 : Entails.eval a c320 := h 319 (by decide)
  have h22 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c104, some c107, some c858, some c330, some c856, some c37, some c295, some c2, some c55, some c138, some c296, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c855, c702, c104, c107, c858, c330, c856, c37, c295, c2, c55, c138, c296] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c858 := derived858 a h
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c856 := derived856 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c104, some c863, some c864, some c136, some c330, some c332, some c38, some c19, some c67, some c295, some c293, some c208, some c144, some c266, some c126, some c14, some c252, some c699, some c133, some c196, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c702, c855, c104, c863, c864, c136, c330, c332, c38, c19, c67, c295, c293, c208, c144, c266, c126, c14, c252, c699, c133, c196] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c863 := derived863 a h
  have h4 : Entails.eval a c864 := derived864 a h
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c144 := h 143 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  have h19 : Entails.eval a c699 := derived699 a h
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨32, by decide⟩, false), (⟨9, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c19, some c718, some c208, some c126, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c38, c19, c718, c208, c126] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c718 := derived718 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c865, some c104, some c107, some c866, some c330, some c335, some c109, some c266, some c295, some c55, some c292, some c203, some c56, some c28, some c108, some c252, some c33, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c702, c855, c865, c104, c107, c866, c330, c335, c109, c266, c295, c55, c292, c203, c56, c28, c108, c252, c33] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c866 := derived866 a h
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨17, by decide⟩, false), (⟨40, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c504, some c55, some c823, some c286, some c292, some c203, some c202, some c56, some c33, some c108, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c855, c504, c55, c823, c286, c292, c203, c202, c56, c33, c108] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c823 := derived823 a h
  have h4 : Entails.eval a c286 := h 285 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c143, some c330, some c335, some c109, some c155, some c868, some c289, some c200, some c152, some c28, some c12, some c203, some c60, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c855, c143, c330, c335, c109, c155, c868, c289, c200, c152, c28, c12, c203, c60] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c868 := derived868 a h
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c865, some c104, some c107, some c867, some c869, some c410, some c38, some c718, some c289, some c832, some c109, some c292, some c332, some c60, some c67, some c108, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c702, c855, c865, c104, c107, c867, c869, c410, c38, c718, c289, c832, c109, c292, c332, c60, c67, c108] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c867 := derived867 a h
  have h6 : Entails.eval a c869 := derived869 a h
  have h7 : Entails.eval a c410 := derived410 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c718 := derived718 a h
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c832 := derived832 a h
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c332 := h 331 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c290, some c55, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c288, c290, c55] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c38, some c55, some c330, some c292, some c18, some c56, some c203, some c108, some c28, some c33, some c252, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c855, c38, c55, c330, c292, c18, c56, c203, c108, c28, c33, c252] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c871, some c292, some c267, some c332, some c18, some c203, some c200, some c28, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c855, c871, c292, c267, c332, c18, c203, c200, c28] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c871 := derived871 a h
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c107, some c104, some c865, some c871, some c138, some c870, some c2, some c192, some c190, some c872, some c289, some c873, some c151, some c60, some c193, some c12, some c699, some c140, some c113, some c295, some c207, some c154, some c128, some c213, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c702, c855, c107, c104, c865, c871, c138, c870, c2, c192, c190, c872, c289, c873, c151, c60, c193, c12, c699, c140, c113, c295, c207, c154, c128, c213] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c871 := derived871 a h
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c870 := derived870 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c872 := derived872 a h
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c873 := derived873 a h
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c699 := derived699 a h
  have h19 : Entails.eval a c140 := h 139 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c295 := h 294 (by decide)
  have h22 : Entails.eval a c207 := h 206 (by decide)
  have h23 : Entails.eval a c154 := h 153 (by decide)
  have h24 : Entails.eval a c128 := h 127 (by decide)
  have h25 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c494, some c193, some c699, some c266, some c295, some c154, some c61, some c722, some c207, some c213, some c128, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c855, c494, c193, c699, c266, c295, c154, c61, c722, c207, c213, c128] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c494 := derived494 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c699 := derived699 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c722 := derived722 a h
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c289, some c288, some c138, some c192, some c875, some c151, some c152, some c292, some c295, some c267, some c266, some c338, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c855, c289, c288, c138, c192, c875, c151, c152, c292, c295, c267, c266, c338] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c875 := derived875 a h
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c38, some c330, some c504, some c292, some c290, some c56, some c138, some c108, some c2, some c96, some c65, some c823, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c855, c702, c38, c330, c504, c292, c290, c56, c138, c108, c2, c96, c65, c823] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c504 := derived504 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c823 := derived823 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c504, some c38, some c46, some c330, some c877, some c55, some c101, some c65, some c18, some c823, some c96, some c89, some c108, some c237, some c56, some c29, some c204, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c855, c702, c504, c38, c46, c330, c877, c55, c101, c65, c18, c823, c96, c89, c108, c237, c56, c29, c204] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c504 := derived504 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c877 := derived877 a h
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c823 := derived823 a h
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  have h18 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c99, some c6, some c494, some c111, some c201, some c210, some c27, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c702, c99, c6, c494, c111, c201, c210, c27] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c494 := derived494 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c99, some c61, some c60, some c879, some c146, some c137, some c10, some c330, some c138, some c111, some c18, some c201, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c702, c855, c99, c61, c60, c879, c146, c137, c10, c330, c138, c111, c18, c201] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c879 := derived879 a h
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c6, some c192, some c146, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c702, c6, c192, c146] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c878, some c105, some c99, some c880, some c291, some c497, some c881, some c138, some c111, some c160, some c201, some c8, some c18, some c137, some c330, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c702, c855, c878, c105, c99, c880, c291, c497, c881, c138, c111, c160, c201, c8, c18, c137, c330] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c880 := derived880 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c497 := derived497 a h
  have h8 : Entails.eval a c881 := derived881 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c878, some c99, some c882, some c292, some c290, some c138, some c267, some c6, some c192, some c332, some c147, some c18, some c193, some c203, some c127, some c132, some c252, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c855, c702, c878, c99, c882, c292, c290, c138, c267, c6, c192, c332, c147, c18, c193, c203, c127, c132, c252] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c332 := h 331 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c127 := h 126 (by decide)
  have h17 : Entails.eval a c132 := h 131 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c874, some c876, some c883, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c874, c876, c883] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c874 := derived874 a h
  have h1 : Entails.eval a c876 := derived876 a h
  have h2 : Entails.eval a c883 := derived883 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c2, some c190, some c37, some c137, some c330, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c702, c855, c2, c190, c37, c137, c330] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c330, some c37, some c101, some c99, some c55, some c721, some c46, some c296, some c25, some c320, some c52, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c855, c702, c330, c37, c101, c99, c55, c721, c46, c296, c25, c320, c52] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c721 := derived721 a h
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c885, some c138, some c111, some c886, some c38, some c137, some c99, some c191, some c54, some c37, some c769, some c725, some c210, some c526, some c521, some c27, some c254, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c702, c855, c885, c138, c111, c886, c38, c137, c99, c191, c54, c37, c769, c725, c210, c526, c521, c27, c254] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c886 := derived886 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c769 := derived769 a h
  have h13 : Entails.eval a c725 := derived725 a h
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c526 := derived526 a h
  have h16 : Entails.eval a c521 := derived521 a h
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c887, some c293, some c44, some c52, some c54, some c101, some c99, some c429, some c861, some c577, some c328, some c320, some c90, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c702, c887, c293, c44, c52, c54, c101, c99, c429, c861, c577, c328, c320, c90] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c887 := derived887 a h
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c429 := derived429 a h
  have h9 : Entails.eval a c861 := derived861 a h
  have h10 : Entails.eval a c577 := derived577 a h
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c874, some c884, some c887, some c888, some c138, some c2, some c190, some c54, some c37, some c45, some c330, some c332, some c314, some c176, some c110, some c158, some c282, some c208, some c193, some c206, some c133, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c702, c855, c874, c884, c887, c888, c138, c2, c190, c54, c37, c45, c330, c332, c314, c176, c110, c158, c282, c208, c193, c206, c133] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c874 := derived874 a h
  have h3 : Entails.eval a c884 := derived884 a h
  have h4 : Entails.eval a c887 := derived887 a h
  have h5 : Entails.eval a c888 := derived888 a h
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c330 := h 329 (by decide)
  have h13 : Entails.eval a c332 := h 331 (by decide)
  have h14 : Entails.eval a c314 := h 313 (by decide)
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c158 := h 157 (by decide)
  have h18 : Entails.eval a c282 := h 281 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c193 := h 192 (by decide)
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c158, some c725, some c208, some c199, some c223, some c27, some c133, some c254, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c110, c158, c725, c208, c199, c223, c27, c133, c254] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c725 := derived725 a h
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c889, some c136, some c332, some c145, some c293, some c267, some c138, some c295, some c144, some c330, some c874, some c45, some c314, some c890, some c6, some c196, some c19, some c67, some c725, some c208, some c108, some c223, some c133, some c48, some c212, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c855, c702, c889, c136, c332, c145, c293, c267, c138, c295, c144, c330, c874, c45, c314, c890, c6, c196, c19, c67, c725, c208, c108, c223, c133, c48, c212] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c874 := derived874 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c314 := h 313 (by decide)
  have h15 : Entails.eval a c890 := derived890 a h
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c196 := h 195 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c67 := h 66 (by decide)
  have h20 : Entails.eval a c725 := derived725 a h
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c108 := h 107 (by decide)
  have h23 : Entails.eval a c223 := h 222 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  have h25 : Entails.eval a c48 := h 47 (by decide)
  have h26 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c889, some c136, some c332, some c330, some c145, some c874, some c891, some c99, some c19, some c67, some c208, some c108, some c126, some c34, some c252, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c855, c702, c889, c136, c332, c330, c145, c874, c891, c99, c19, c67, c208, c108, c126, c34, c252] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c874 := derived874 a h
  have h8 : Entails.eval a c891 := derived891 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c889, some c136, some c330, some c332, some c892, some c38, some c137, some c264, some c99, some c105, some c8, some c45, some c144, some c314, some c297, some c48, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c702, c855, c889, c136, c330, c332, c892, c38, c137, c264, c99, c105, c8, c45, c144, c314, c297, c48] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c330 := h 329 (by decide)
  have h5 : Entails.eval a c332 := h 331 (by decide)
  have h6 : Entails.eval a c892 := derived892 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c144 := h 143 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c38, some c137, some c105, some c6, some c8, some c138, some c111, some c160, some c201, some c497, some c27, some c291, some c210, some c61, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c702, c855, c38, c137, c105, c6, c8, c138, c111, c160, c201, c497, c27, c291, c210, c61] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c497 := derived497 a h
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c138, some c111, some c201, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c138, c111, c201] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c292, some c290, some c267, some c281, some c324, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c855, c292, c290, c267, c281, c324] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨34, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c48, some c318, some c896, some c146, some c60, some c10, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c855, c702, c48, c318, c896, c146, c60, c10] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c896 := derived896 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c895, some c894, some c105, some c8, some c897, some c291, some c202, some c147, some c34, some c199, some c120, some c304, some c118, some c725, some c258, some c703, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c855, c895, c894, c105, c8, c897, c291, c202, c147, c34, c199, c120, c304, c118, c725, c258, c703] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c894 := derived894 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c897 := derived897 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c725 := derived725 a h
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c703 := derived703 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨35, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c898, some c504, some c46, some c823, some c96, some c89, some c108, some c237, some c56, some c29, some c204, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c855, c898, c504, c46, c823, c96, c89, c108, c237, c56, c29, c204] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c898 := derived898 a h
  have h2 : Entails.eval a c504 := derived504 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c823 := derived823 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c893, some c889, some c874, some c894, some c330, some c335, some c156, some c109, some c155, some c899, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c855, c893, c889, c874, c894, c330, c335, c156, c109, c155, c899] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c893 := derived893 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c874 := derived874 a h
  have h4 : Entails.eval a c894 := derived894 a h
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c899 := derived899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c893, some c889, some c874, some c900, some c99, some c719, some c504, some c38, some c108, some c330, some c96, some c156, some c823, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c702, c855, c893, c889, c874, c900, c99, c719, c504, c38, c108, c330, c96, c156, c823] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c893 := derived893 a h
  have h3 : Entails.eval a c889 := derived889 a h
  have h4 : Entails.eval a c874 := derived874 a h
  have h5 : Entails.eval a c900 := derived900 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c719 := derived719 a h
  have h8 : Entails.eval a c504 := derived504 a h
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c823 := derived823 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c99, some c101, some c893, some c901, some c288, some c889, some c335, some c869, some c266, some c295, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c702, c855, c99, c101, c893, c901, c288, c889, c335, c869, c266, c295] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c893 := derived893 a h
  have h5 : Entails.eval a c901 := derived901 a h
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c889 := derived889 a h
  have h8 : Entails.eval a c335 := h 334 (by decide)
  have h9 : Entails.eval a c869 := derived869 a h
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c893, some c901, some c288, some c889, some c874, some c101, some c99, some c902, some c409, some c718, some c866, some c832, some c52, some c292, some c50, some c44, some c328, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c702, c893, c901, c288, c889, c874, c101, c99, c902, c409, c718, c866, c832, c52, c292, c50, c44, c328] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c893 := derived893 a h
  have h2 : Entails.eval a c901 := derived901 a h
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c889 := derived889 a h
  have h5 : Entails.eval a c874 := derived874 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c902 := derived902 a h
  have h9 : Entails.eval a c409 := derived409 a h
  have h10 : Entails.eval a c718 := derived718 a h
  have h11 : Entails.eval a c866 := derived866 a h
  have h12 : Entails.eval a c832 := derived832 a h
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c718, some c866, some c27, some c61, some c152, some c258, some c12, some c125, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c19, c718, c866, c27, c61, c152, c258, c12, c125] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c866 := derived866 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c289, some c904, some c105, some c6, some c61, some c110, some c200, some c208, some c27, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c702, c289, c904, c105, c6, c61, c110, c200, c208, c27] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c904 := derived904 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c874, some c889, some c893, some c901, some c289, some c288, some c138, some c903, some c905, some c330, some c335, some c155, some c266, some c295, some c61, some c152, some c12, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c855, c874, c889, c893, c901, c289, c288, c138, c903, c905, c330, c335, c155, c266, c295, c61, c152, c12] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c874 := derived874 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c893 := derived893 a h
  have h4 : Entails.eval a c901 := derived901 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c903 := derived903 a h
  have h9 : Entails.eval a c905 := derived905 a h
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c330, some c335, some c64, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c855, c330, c335, c64] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c330 := h 329 (by decide)
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨32, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨34, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c627, some c104, some c289, some c207, some c61, some c152, some c110, some c7, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c702, c627, c104, c289, c207, c61, c152, c110, c7] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c627 := derived627 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, false), (⟨33, by decide⟩, false), (⟨29, by decide⟩, false), (⟨34, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c627, some c137, some c815, some c6, some c213, some c111, some c895, some c601, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c702, c855, c627, c137, c815, c6, c213, c111, c895, c601] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c627 := derived627 a h
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c815 := derived815 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c895 := derived895 a h
  have h9 : Entails.eval a c601 := derived601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c906, some c907, some c41, some c64, some c22, some c909, some c295, some c908, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c906, c907, c41, c64, c22, c909, c295, c908] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c906 := derived906 a h
  have h1 : Entails.eval a c907 := derived907 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c909 := derived909 a h
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨31, by decide⟩, false), (⟨26, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c204, some c220, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c200, c204, c220] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c143, some c910, some c338, some c906, some c907, some c289, some c288, some c267, some c911, some c26, some c908, some c49, some c323, some c326, some c286, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c855, c143, c910, c338, c906, c907, c289, c288, c267, c911, c26, c908, c49, c323, c326, c286] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c910 := derived910 a h
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c906 := derived906 a h
  have h5 : Entails.eval a c907 := derived907 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c911 := derived911 a h
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c908 := derived908 a h
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c326 := h 325 (by decide)
  have h15 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c910, some c338, some c906, some c907, some c912, some c38, some c137, some c264, some c104, some c291, some c61, some c152, some c7, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c855, c702, c910, c338, c906, c907, c912, c38, c137, c264, c104, c291, c61, c152, c7] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c910 := derived910 a h
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c906 := derived906 a h
  have h5 : Entails.eval a c907 := derived907 a h
  have h6 : Entails.eval a c912 := derived912 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, false), (⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c38, some c137, some c104, some c6, some c138, some c111, some c895, some c210, some c27, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c702, c38, c137, c104, c6, c138, c111, c895, c210, c27] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c895 := derived895 a h
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c906, some c907, some c910, some c338, some c913, some c914, some c289, some c288, some c295, some c267, some c49, some c292, some c323, some c62, some c282, some c285, some c107, some c355, some c350, some c89, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c855, c702, c906, c907, c910, c338, c913, c914, c289, c288, c295, c267, c49, c292, c323, c62, c282, c285, c107, c355, c350, c89] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c907 := derived907 a h
  have h4 : Entails.eval a c910 := derived910 a h
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c913 := derived913 a h
  have h7 : Entails.eval a c914 := derived914 a h
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c285 := h 284 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c355 := h 354 (by decide)
  have h20 : Entails.eval a c350 := h 349 (by decide)
  have h21 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c101, some c99, some c871, some c138, some c2, some c409, some c38, some c718, some c832, some c289, some c109, some c292, some c332, some c60, some c67, some c102, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c702, c855, c101, c99, c871, c138, c2, c409, c38, c718, c832, c289, c109, c292, c332, c60, c67, c102] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c871 := derived871 a h
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c409 := derived409 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c718 := derived718 a h
  have h10 : Entails.eval a c832 := derived832 a h
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c332 := h 331 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c289, some c295, some c152, some c385, some c199, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c289, c295, c152, c385, c199] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c289 := h 288 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c385 := derived385 a h
  have h4 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c906, some c915, some c101, some c99, some c871, some c138, some c2, some c916, some c330, some c335, some c109, some c720, some c155, some c41, some c22, some c102, some c917, some c504, some c55, some c48, some c203, some c202, some c33, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c702, c855, c906, c915, c101, c99, c871, c138, c2, c916, c330, c335, c109, c720, c155, c41, c22, c102, c917, c504, c55, c48, c203, c202, c33] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c915 := derived915 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c871 := derived871 a h
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c916 := derived916 a h
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c720 := derived720 a h
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c41 := h 40 (by decide)
  have h16 : Entails.eval a c22 := h 21 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  have h18 : Entails.eval a c917 := derived917 a h
  have h19 : Entails.eval a c504 := derived504 a h
  have h20 : Entails.eval a c55 := h 54 (by decide)
  have h21 : Entails.eval a c48 := h 47 (by decide)
  have h22 : Entails.eval a c203 := h 202 (by decide)
  have h23 : Entails.eval a c202 := h 201 (by decide)
  have h24 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c918, some c906, some c37, some c136, some c101, some c99, some c885, some c429, some c38, some c55, some c138, some c209, some c335, some c856, some c296, some c35, some c160, some c297, some c385, some c56, some c5, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c702, c855, c918, c906, c37, c136, c101, c99, c885, c429, c38, c55, c138, c209, c335, c856, c296, c35, c160, c297, c385, c56, c5] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c906 := derived906 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c885 := derived885 a h
  have h9 : Entails.eval a c429 := derived429 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c335 := h 334 (by decide)
  have h15 : Entails.eval a c856 := derived856 a h
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c297 := h 296 (by decide)
  have h20 : Entails.eval a c385 := derived385 a h
  have h21 : Entails.eval a c56 := h 55 (by decide)
  have h22 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c918, some c906, some c919, some c330, some c332, some c38, some c264, some c99, some c297, some c53, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c855, c702, c918, c906, c919, c330, c332, c38, c264, c99, c297, c53] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c906 := derived906 a h
  have h4 : Entails.eval a c919 := derived919 a h
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c330, some c38, some c137, some c104, some c99, some c6, some c54, some c45, some c138, some c314, some c296, some c534, some c285, some c315, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c702, c855, c330, c38, c137, c104, c99, c6, c54, c45, c138, c314, c296, c534, c285, c315] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  have h13 : Entails.eval a c534 := derived534 a h
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c918, some c920, some c921, some c37, some c136, some c101, some c99, some c885, some c504, some c55, some c138, some c48, some c296, some c3, some c152, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c702, c855, c918, c920, c921, c37, c136, c101, c99, c885, c504, c55, c138, c48, c296, c3, c152] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c920 := derived920 a h
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c885 := derived885 a h
  have h10 : Entails.eval a c504 := derived504 a h
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨28, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c922, some c918, some c37, some c136, some c101, some c99, some c2, some c429, some c138, some c205, some c293, some c28, some c152, some c209, some c3, some c60, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c702, c922, c918, c37, c136, c101, c99, c2, c429, c138, c205, c293, c28, c152, c209, c3, c60] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c429 := derived429 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c209 := h 208 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c99, some c922, some c918, some c293, some c577, some c145, some c429, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c702, c99, c922, c918, c293, c577, c145, c429] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c918 := derived918 a h
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c577 := derived577 a h
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c429 := derived429 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c923, some c332, some c330, some c922, some c918, some c906, some c99, some c67, some c102, some c48, some c924, some c138, some c2, some c145, some c295, some c266, some c49, some c323, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c702, c855, c923, c332, c330, c922, c918, c906, c99, c67, c102, c48, c924, c138, c2, c145, c295, c266, c49, c323] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c923 := derived923 a h
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c330 := h 329 (by decide)
  have h5 : Entails.eval a c922 := derived922 a h
  have h6 : Entails.eval a c918 := derived918 a h
  have h7 : Entails.eval a c906 := derived906 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c924 := derived924 a h
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c49 := h 48 (by decide)
  have h19 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c922, some c918, some c906, some c923, some c330, some c332, some c925, some c53, some c295, some c145, some c152, some c191, some c193, some c158, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c855, c922, c918, c906, c923, c330, c332, c925, c53, c295, c145, c152, c191, c193, c158] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c906 := derived906 a h
  have h4 : Entails.eval a c923 := derived923 a h
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c925 := derived925 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c906, some c918, some c922, some c926, some c294, some c856, some c53, some c41, some c101, some c99, some c924, some c338, some c62, some c19, some c67, some c138, some c267, some c206, some c102, some c2, some c33, some c145, some c216, some c215, some c126, some c223, some c251, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c702, c855, c906, c918, c922, c926, c294, c856, c53, c41, c101, c99, c924, c338, c62, c19, c67, c138, c267, c206, c102, c2, c33, c145, c216, c215, c126, c223, c251] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c918 := derived918 a h
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c926 := derived926 a h
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c856 := derived856 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c924 := derived924 a h
  have h13 : Entails.eval a c338 := h 337 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c267 := h 266 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c102 := h 101 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c33 := h 32 (by decide)
  have h23 : Entails.eval a c145 := h 144 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  have h25 : Entails.eval a c215 := h 214 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  have h27 : Entails.eval a c223 := h 222 (by decide)
  have h28 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c927, some c101, some c99, some c717, some c764, some c262, some c116, some c295, some c208, some c856, some c19, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c702, c927, c101, c99, c717, c764, c262, c116, c295, c208, c856, c19] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c927 := derived927 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c717 := derived717 a h
  have h5 : Entails.eval a c764 := derived764 a h
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c856 := derived856 a h
  have h11 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨32, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c67, some c206, some c208, some c108, some c34, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c19, c67, c206, c208, c108, c34] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨51, by decide⟩, true), (⟨34, by decide⟩, true), (⟨38, by decide⟩, true), (⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c37, some c45, some c314, some c332, some c295, some c293, some c53, some c282, some c410, some c929, some c105, some c777, some c110, some c206, some c208, some c34, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c855, c702, c37, c45, c314, c332, c295, c293, c53, c282, c410, c929, c105, c777, c110, c206, c208, c34] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c332 := h 331 (by decide)
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c410 := derived410 a h
  have h11 : Entails.eval a c929 := derived929 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c777 := derived777 a h
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c208 := h 207 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c927, some c928, some c37, some c45, some c331, some c329, some c313, some c930, some c54, some c143, some c107, some c104, some c764, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c702, c927, c928, c37, c45, c331, c329, c313, c930, c54, c143, c107, c104, c764] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c927 := derived927 a h
  have h2 : Entails.eval a c928 := derived928 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c329 := h 328 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c930 := derived930 a h
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c764 := derived764 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c37, some c45, some c331, some c329, some c332, some c314, some c313, some c38, some c137, some c264, some c104, some c777, some c54, some c297, some c534, some c282, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c855, c702, c37, c45, c331, c329, c332, c314, c313, c38, c137, c264, c104, c777, c54, c297, c534, c282] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c777 := derived777 a h
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c534 := derived534 a h
  have h17 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c927, some c931, some c932, some c101, some c99, some c717, some c764, some c38, some c504, some c46, some c55, some c262, some c116, some c856, some c317, some c296, some c216, some c282, some c23, some c297, some c56, some c847, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c702, c855, c927, c931, c932, c101, c99, c717, c764, c38, c504, c46, c55, c262, c116, c856, c317, c296, c216, c282, c23, c297, c56, c847] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c927 := derived927 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c932 := derived932 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c717 := derived717 a h
  have h8 : Entails.eval a c764 := derived764 a h
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c504 := derived504 a h
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c856 := derived856 a h
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c282 := h 281 (by decide)
  have h20 : Entails.eval a c23 := h 22 (by decide)
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c56 := h 55 (by decide)
  have h23 : Entails.eval a c847 := derived847 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c933, some c927, some c101, some c99, some c717, some c719, some c764, some c871, some c55, some c156, some c292, some c2, some c5, some c150, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c702, c933, c927, c101, c99, c717, c719, c764, c871, c55, c156, c292, c2, c5, c150] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c933 := derived933 a h
  have h2 : Entails.eval a c927 := derived927 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c717 := derived717 a h
  have h6 : Entails.eval a c719 := derived719 a h
  have h7 : Entails.eval a c764 := derived764 a h
  have h8 : Entails.eval a c871 := derived871 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c934, some c933, some c927, some c38, some c330, some c907, some c334, some c872, some c65, some c107, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c855, c702, c934, c933, c927, c38, c330, c907, c334, c872, c65, c107] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c934 := derived934 a h
  have h3 : Entails.eval a c933 := derived933 a h
  have h4 : Entails.eval a c927 := derived927 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c330 := h 329 (by decide)
  have h7 : Entails.eval a c907 := derived907 a h
  have h8 : Entails.eval a c334 := h 333 (by decide)
  have h9 : Entails.eval a c872 := derived872 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c935, some c104, some c934, some c933, some c927, some c18, some c65, some c334, some c337, some c137, some c263, some c540, some c6, some c292, some c203, some c497, some c150, some c114, some c64, some c194, some c8, some c155, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c702, c855, c935, c104, c934, c933, c927, c18, c65, c334, c337, c137, c263, c540, c6, c292, c203, c497, c150, c114, c64, c194, c8, c155] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c935 := derived935 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c934 := derived934 a h
  have h5 : Entails.eval a c933 := derived933 a h
  have h6 : Entails.eval a c927 := derived927 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c334 := h 333 (by decide)
  have h10 : Entails.eval a c337 := h 336 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c540 := derived540 a h
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c497 := derived497 a h
  have h18 : Entails.eval a c150 := h 149 (by decide)
  have h19 : Entails.eval a c114 := h 113 (by decide)
  have h20 : Entails.eval a c64 := h 63 (by decide)
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c933, some c927, some c936, some c331, some c329, some c332, some c263, some c264, some c292, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c855, c933, c927, c936, c331, c329, c332, c263, c264, c292] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c933 := derived933 a h
  have h2 : Entails.eval a c927 := derived927 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c933, some c937, some c288, some c289, some c105, some c61, some c295, some c208, some c149, some c110, some c8, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c933, c937, c288, c289, c105, c61, c295, c208, c149, c110, c8] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c933 := derived933 a h
  have h1 : Entails.eval a c937 := derived937 a h
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨31, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c258, some c220, some c110, some c213, some c196, some c149, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c258, c220, c110, c213, c196, c149] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c258 := h 257 (by decide)
  have h1 : Entails.eval a c220 := h 219 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c927, some c717, some c332, some c329, some c331, some c933, some c937, some c288, some c289, some c292, some c911, some c42, some c141, some c107, some c10, some c27, some c148, some c939, some c26, some c938, some c19, some c67, some c208, some c108, some c61, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c855, c702, c927, c717, c332, c329, c331, c933, c937, c288, c289, c292, c911, c42, c141, c107, c10, c27, c148, c939, c26, c938, c19, c67, c208, c108, c61] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c927 := derived927 a h
  have h3 : Entails.eval a c717 := derived717 a h
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c933 := derived933 a h
  have h8 : Entails.eval a c937 := derived937 a h
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c911 := derived911 a h
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c939 := derived939 a h
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c938 := derived938 a h
  have h22 : Entails.eval a c19 := h 18 (by decide)
  have h23 : Entails.eval a c67 := h 66 (by decide)
  have h24 : Entails.eval a c208 := h 207 (by decide)
  have h25 : Entails.eval a c108 := h 107 (by decide)
  have h26 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c332, some c940, some c142, some c43, some c927, some c717, some c329, some c331, some c933, some c937, some c288, some c289, some c108, some c14, some c61, some c295, some c149, some c905, some c190, some c192, some c157, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c855, c332, c940, c142, c43, c927, c717, c329, c331, c933, c937, c288, c289, c108, c14, c61, c295, c149, c905, c190, c192, c157] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c927 := derived927 a h
  have h6 : Entails.eval a c717 := derived717 a h
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c933 := derived933 a h
  have h10 : Entails.eval a c937 := derived937 a h
  have h11 : Entails.eval a c288 := h 287 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c905 := derived905 a h
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c192 := h 191 (by decide)
  have h21 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, true), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c927, some c717, some c329, some c331, some c933, some c141, some c157, some c114, some c6, some c190, some c203, some c19, some c126, some c26, some c258, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c702, c927, c717, c329, c331, c933, c141, c157, c114, c6, c190, c203, c19, c126, c26, c258] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c927 := derived927 a h
  have h2 : Entails.eval a c717 := derived717 a h
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c933 := derived933 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c941, some c332, some c940, some c142, some c43, some c927, some c717, some c329, some c331, some c933, some c942, some c16, some c23, some c42, some c66, some c203, some c6, some c27, some c26, some c110, some c258, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c855, c702, c941, c332, c940, c142, c43, c927, c717, c329, c331, c933, c942, c16, c23, c42, c66, c203, c6, c27, c26, c110, c258] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c941 := derived941 a h
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c940 := derived940 a h
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c717 := derived717 a h
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c933 := derived933 a h
  have h12 : Entails.eval a c942 := derived942 a h
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c110 := h 109 (by decide)
  have h22 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c332, some c940, some c142, some c43, some c933, some c937, some c288, some c289, some c943, some c148, some c199, some c13, some c149, some c61, some c295, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c855, c332, c940, c142, c43, c933, c937, c288, c289, c943, c148, c199, c13, c149, c61, c295] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c332 := h 331 (by decide)
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c933 := derived933 a h
  have h6 : Entails.eval a c937 := derived937 a h
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c943 := derived943 a h
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c927, some c331, some c329, some c944, some c107, some c104, some c66, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c702, c927, c331, c329, c944, c107, c104, c66] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c927 := derived927 a h
  have h2 : Entails.eval a c331 := h 330 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c945, some c933, some c937, some c288, some c289, some c927, some c107, some c104, some c764, some c143, some c116, some c156, some c295, some c208, some c494, some c19, some c28, some c118, some c335, some c216, some c304, some c274, some c41, some c140, some c60, some c173, some c12, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c702, c855, c945, c933, c937, c288, c289, c927, c107, c104, c764, c143, c116, c156, c295, c208, c494, c19, c28, c118, c335, c216, c304, c274, c41, c140, c60, c173, c12] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c945 := derived945 a h
  have h3 : Entails.eval a c933 := derived933 a h
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c764 := derived764 a h
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c494 := derived494 a h
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c118 := h 117 (by decide)
  have h20 : Entails.eval a c335 := h 334 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  have h22 : Entails.eval a c304 := h 303 (by decide)
  have h23 : Entails.eval a c274 := h 273 (by decide)
  have h24 : Entails.eval a c41 := h 40 (by decide)
  have h25 : Entails.eval a c140 := h 139 (by decide)
  have h26 : Entails.eval a c60 := h 59 (by decide)
  have h27 : Entails.eval a c173 := h 172 (by decide)
  have h28 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c946, some c945, some c933, some c937, some c288, some c289, some c927, some c334, some c143, some c116, some c156, some c65, some c208, some c494, some c101, some c99, some c2, some c118, some c721, some c119, some c303, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c702, c946, c945, c933, c937, c288, c289, c927, c334, c143, c116, c156, c65, c208, c494, c101, c99, c2, c118, c721, c119, c303] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c945 := derived945 a h
  have h3 : Entails.eval a c933 := derived933 a h
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c334 := h 333 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c494 := derived494 a h
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c118 := h 117 (by decide)
  have h19 : Entails.eval a c721 := derived721 a h
  have h20 : Entails.eval a c119 := h 118 (by decide)
  have h21 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c947, some c945, some c937, some c933, some c927, some c718, some c19, some c18, some c101, some c764, some c143, some c116, some c208, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c702, c947, c945, c937, c933, c927, c718, c19, c18, c101, c764, c143, c116, c208] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c947 := derived947 a h
  have h2 : Entails.eval a c945 := derived945 a h
  have h3 : Entails.eval a c937 := derived937 a h
  have h4 : Entails.eval a c933 := derived933 a h
  have h5 : Entails.eval a c927 := derived927 a h
  have h6 : Entails.eval a c718 := derived718 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c764 := derived764 a h
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c927, some c933, some c937, some c289, some c288, some c945, some c946, some c947, some c948, some c99, some c18, some c65, some c200, some c337, some c110, some c219, some c6, some c494, some c255, some c148, some c220, some c196, some c338, some c155, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c702, c855, c927, c933, c937, c289, c288, c945, c946, c947, c948, c99, c18, c65, c200, c337, c110, c219, c6, c494, c255, c148, c220, c196, c338, c155] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c927 := derived927 a h
  have h3 : Entails.eval a c933 := derived933 a h
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c945 := derived945 a h
  have h8 : Entails.eval a c946 := derived946 a h
  have h9 : Entails.eval a c947 := derived947 a h
  have h10 : Entails.eval a c948 := derived948 a h
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c337 := h 336 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c494 := derived494 a h
  have h20 : Entails.eval a c255 := h 254 (by decide)
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c220 := h 219 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  have h24 : Entails.eval a c338 := h 337 (by decide)
  have h25 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨38, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c533, some c540, some c104, some c289, some c200, some c148, some c110, some c7, some c196, some c61, some c149, some c295, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c702, c949, c533, c540, c104, c289, c200, c148, c110, c7, c196, c61, c149, c295] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c533 := derived533 a h
  have h3 : Entails.eval a c540 := derived540 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c855, some c99, some c18, some c37, some c540, some c533, some c950, some c137, some c263, some c197, some c292, some c203, some c497, some c150, some c114, some c155, some c194, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c702, c949, c855, c99, c18, c37, c540, c533, c950, c137, c263, c197, c292, c203, c497, c150, c114, c155, c194] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c855 := derived855 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c540 := derived540 a h
  have h7 : Entails.eval a c533 := derived533 a h
  have h8 : Entails.eval a c950 := derived950 a h
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c497 := derived497 a h
  have h15 : Entails.eval a c150 := h 149 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c949, some c104, some c99, some c37, some c18, some c65, some c951, some c337, some c895, some c195, some c137, some c110, some c200, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c702, c949, c104, c99, c37, c18, c65, c951, c337, c895, c195, c137, c110, c200] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c951 := derived951 a h
  have h8 : Entails.eval a c337 := h 336 (by decide)
  have h9 : Entails.eval a c895 := derived895 a h
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c952, some c718, some c916, some c18, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c952, c718, c916, c18] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c952 := derived952 a h
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c916 := derived916 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c952, some c19, some c38, some c953, some c37, some c136, some c2, some c429, some c138, some c205, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c702, c952, c19, c38, c953, c37, c136, c2, c429, c138, c205] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c952 := derived952 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c953 := derived953 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c429 := derived429 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c855, some c949, some c954, some c952, some c38, some c37, some c136, some c101, some c2, some c764, some c262, some c295, some c293, some c261, some c149, some c338, some c197, some c67, some c158, some c5, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c702, c855, c949, c954, c952, c38, c37, c136, c101, c2, c764, c262, c295, c293, c261, c149, c338, c197, c67, c158, c5] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c855 := derived855 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c954 := derived954 a h
  have h4 : Entails.eval a c952 := derived952 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c764 := derived764 a h
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c338 := h 337 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  have h19 : Entails.eval a c158 := h 157 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c702, some c952, some c38, some c19, some c954, some c955, some c718, some c289, some c288, some c18, some c109, some c494, some c101, some c2, some c764, some c148, some c218, some c193, some c258, some c699, some c217, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c855, c702, c952, c38, c19, c954, c955, c718, c289, c288, c18, c109, c494, c101, c2, c764, c148, c218, c193, c258, c699, c217] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c702 := derived702 a h
  have h2 : Entails.eval a c952 := derived952 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c954 := derived954 a h
  have h6 : Entails.eval a c955 := derived955 a h
  have h7 : Entails.eval a c718 := derived718 a h
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c494 := derived494 a h
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c764 := derived764 a h
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c699 := derived699 a h
  have h21 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived956

end CochromaticTwenty.Certificates.B16_4_0
