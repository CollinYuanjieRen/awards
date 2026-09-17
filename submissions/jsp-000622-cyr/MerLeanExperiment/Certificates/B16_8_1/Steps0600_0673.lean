import MerLeanExperiment.Certificates.B16_8_1.Steps0500_0599

/-! Generated from the actual pinned b16_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c889 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨41, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c886, some c885, some c134, some c135, some c888, some c266, some c462, some c120, some c267, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c763, c886, c885, c134, c135, c888, c266, c462, c120, c267] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c886 := derived886 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c888 := derived888 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c462 := derived462 a h
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c885, some c266, some c265, some c459, some c462, some c270, some c67, some c499, some c267, some c387, some c365, some c419, some c440, some c403, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c763, c859, c885, c266, c265, c459, c462, c270, c67, c499, c267, c387, c365, c419, c440, c403] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c459 := derived459 a h
  have h6 : Entails.eval a c462 := derived462 a h
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c499 := derived499 a h
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c387 := derived387 a h
  have h12 : Entails.eval a c365 := derived365 a h
  have h13 : Entails.eval a c419 := derived419 a h
  have h14 : Entails.eval a c440 := derived440 a h
  have h15 : Entails.eval a c403 := derived403 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c889, some c886, some c885, some c268, some c272, some c66, some c496, some c140, some c498, some c67, some c499, some c387, some c365, some c419, some c492, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c763, c859, c889, c886, c885, c268, c272, c66, c496, c140, c498, c67, c499, c387, c365, c419, c492] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c886 := derived886 a h
  have h4 : Entails.eval a c885 := derived885 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c496 := derived496 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c498 := derived498 a h
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c499 := derived499 a h
  have h13 : Entails.eval a c387 := derived387 a h
  have h14 : Entails.eval a c365 := derived365 a h
  have h15 : Entails.eval a c419 := derived419 a h
  have h16 : Entails.eval a c492 := derived492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨43, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c258, some c278, some c287, some c69, some c123, some c443, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c859, c258, c278, c287, c69, c123, c443] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c443 := derived443 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c885, some c886, some c889, some c890, some c892, some c267, some c891, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c885, c886, c889, c890, c892, c267, c891] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c885 := derived885 a h
  have h1 : Entails.eval a c886 := derived886 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c890 := derived890 a h
  have h4 : Entails.eval a c892 := derived892 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c891 := derived891 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c14, some c71, some c11, some c106, some c459, some c439, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c859, c763, c14, c71, c11, c106, c459, c439] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c459 := derived459 a h
  have h7 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c118, some c134, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c113, c118, c134] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨12, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c443, some c894, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c859, c443, c894] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c443 := derived443 a h
  have h2 : Entails.eval a c894 := derived894 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c885, some c893, some c50, some c58, some c278, some c485, some c59, some c896, some c895, some c273, some c258, some c462, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c859, c763, c885, c893, c50, c58, c278, c485, c59, c896, c895, c273, c258, c462] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c893 := derived893 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c485 := derived485 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c896 := derived896 a h
  have h10 : Entails.eval a c895 := derived895 a h
  have h11 : Entails.eval a c273 := h 272 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c462 := derived462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c125, some c107, some c273, some c272, some c113, some c412, some c132, some c271, some c556, some c259, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c859, c125, c107, c273, c272, c113, c412, c132, c271, c556, c259] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c412 := derived412 a h
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c897, some c107, some c885, some c50, some c58, some c278, some c272, some c125, some c59, some c898, some c11, some c52, some c71, some c404, some c459, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c859, c763, c897, c107, c885, c50, c58, c278, c272, c125, c59, c898, c11, c52, c71, c404, c459] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c897 := derived897 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c885 := derived885 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c898 := derived898 a h
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c404 := derived404 a h
  have h16 : Entails.eval a c459 := derived459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨6, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c107, some c272, some c267, some c268, some c125, some c492, some c397, some c721, some c127, some c132, some c498, some c56, some c18, some c120, some c118, some c142, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c859, c763, c107, c272, c267, c268, c125, c492, c397, c721, c127, c132, c498, c56, c18, c120, c118, c142] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c492 := derived492 a h
  have h8 : Entails.eval a c397 := derived397 a h
  have h9 : Entails.eval a c721 := derived721 a h
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c498 := derived498 a h
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c885, some c897, some c107, some c899, some c886, some c268, some c267, some c272, some c66, some c900, some c521, some c287, some c283, some c419, some c108, some c127, some c265, some c493, some c497, some c30, some c18, some c120, some c116, some c142, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c859, c763, c885, c897, c107, c899, c886, c268, c267, c272, c66, c900, c521, c287, c283, c419, c108, c127, c265, c493, c497, c30, c18, c120, c116, c142] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c897 := derived897 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c899 := derived899 a h
  have h6 : Entails.eval a c886 := derived886 a h
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c900 := derived900 a h
  have h12 : Entails.eval a c521 := derived521 a h
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c419 := derived419 a h
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c493 := derived493 a h
  have h20 : Entails.eval a c497 := derived497 a h
  have h21 : Entails.eval a c30 := h 29 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c120 := h 119 (by decide)
  have h24 : Entails.eval a c116 := h 115 (by decide)
  have h25 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c901, some c268, some c267, some c60, some c300, some c66, some c336, some c82, some c67, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c763, c901, c268, c267, c60, c300, c66, c336, c82, c67] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c901 := derived901 a h
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c300 := derived300 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c336 := derived336 a h
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c901, some c53, some c80, some c299, some c885, some c278, some c287, some c520, some c123, some c78, some c443, some c630, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c763, c859, c901, c53, c80, c299, c885, c278, c287, c520, c123, c78, c443, c630] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c901 := derived901 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c299 := derived299 a h
  have h6 : Entails.eval a c885 := derived885 a h
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c520 := derived520 a h
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c443 := derived443 a h
  have h13 : Entails.eval a c630 := derived630 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c902, some c903, some c297, some c258, some c510, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c763, c859, c902, c903, c297, c258, c510] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c902 := derived902 a h
  have h3 : Entails.eval a c903 := derived903 a h
  have h4 : Entails.eval a c297 := derived297 a h
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c510 := derived510 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c904, some c901, some c53, some c107, some c299, some c903, some c80, some c258, some c459, some c510, some c112, some c512, some c139, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c859, c763, c904, c901, c53, c107, c299, c903, c80, c258, c459, c510, c112, c512, c139] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c904 := derived904 a h
  have h3 : Entails.eval a c901 := derived901 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c299 := derived299 a h
  have h7 : Entails.eval a c903 := derived903 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c459 := derived459 a h
  have h11 : Entails.eval a c510 := derived510 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c512 := derived512 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c139, some c137, some c125, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c859, c139, c137, c125] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c125, some c127, some c132, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c859, c125, c127, c132] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c904, some c901, some c481, some c907, some c2, some c71, some c73, some c78, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c859, c904, c901, c481, c907, c2, c71, c73, c78] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c901 := derived901 a h
  have h3 : Entails.eval a c481 := derived481 a h
  have h4 : Entails.eval a c907 := derived907 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c904, some c51, some c908, some c512, some c112, some c906, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c763, c904, c51, c908, c512, c112, c906] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c512 := derived512 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c906 := derived906 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c905, some c904, some c276, some c909, some c273, some c458, some c271, some c402, some c412, some c439, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c763, c905, c904, c276, c909, c273, c458, c271, c402, c412, c439] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c905 := derived905 a h
  have h2 : Entails.eval a c904 := derived904 a h
  have h3 : Entails.eval a c276 := h 275 (by decide)
  have h4 : Entails.eval a c909 := derived909 a h
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c458 := derived458 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c402 := derived402 a h
  have h9 : Entails.eval a c412 := derived412 a h
  have h10 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c904, some c901, some c910, some c60, some c458, some c271, some c82, some c67, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c763, c904, c901, c910, c60, c458, c271, c82, c67] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c901 := derived901 a h
  have h3 : Entails.eval a c910 := derived910 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c458 := derived458 a h
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c901, some c911, some c52, some c78, some c904, some c292, some c104, some c106, some c905, some c272, some c273, some c113, some c259, some c11, some c397, some c564, some c64, some c495, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c859, c901, c911, c52, c78, c904, c292, c104, c106, c905, c272, c273, c113, c259, c11, c397, c564, c64, c495] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c901 := derived901 a h
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c904 := derived904 a h
  have h6 : Entails.eval a c292 := derived292 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c905 := derived905 a h
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c273 := h 272 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c397 := derived397 a h
  have h16 : Entails.eval a c564 := derived564 a h
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c905, some c904, some c901, some c911, some c292, some c106, some c912, some c60, some c112, some c276, some c137, some c113, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c763, c905, c904, c901, c911, c292, c106, c912, c60, c112, c276, c137, c113] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c905 := derived905 a h
  have h2 : Entails.eval a c904 := derived904 a h
  have h3 : Entails.eval a c901 := derived901 a h
  have h4 : Entails.eval a c911 := derived911 a h
  have h5 : Entails.eval a c292 := derived292 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c912 := derived912 a h
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c763, some c885, some c901, some c904, some c905, some c913, some c278, some c287, some c482, some c256, some c82, some c276, some c809, some c66, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c859, c763, c885, c901, c904, c905, c913, c278, c287, c482, c256, c82, c276, c809, c66] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c901 := derived901 a h
  have h4 : Entails.eval a c904 := derived904 a h
  have h5 : Entails.eval a c905 := derived905 a h
  have h6 : Entails.eval a c913 := derived913 a h
  have h7 : Entails.eval a c278 := h 277 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c482 := derived482 a h
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c809 := derived809 a h
  have h14 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c763, some c51, some c58, some c283, some c79, some c81, some c53, some c73, some c82, some c517, some c55, some c542, some c240, some c25, some c203, some c35, some c36, some c219, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c914, c859, c763, c51, c58, c283, c79, c81, c53, c73, c82, c517, c55, c542, c240, c25, c203, c35, c36, c219] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c517 := derived517 a h
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c542 := derived542 a h
  have h14 : Entails.eval a c240 := h 239 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨44, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c915, some c272, some c415, some c273, some c81, some c829, some c334, some c73, some c277, some c104, some c701, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c914, c859, c915, c272, c415, c273, c81, c829, c334, c73, c277, c104, c701] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c915 := derived915 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c415 := derived415 a h
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c829 := derived829 a h
  have h8 : Entails.eval a c334 := derived334 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c277 := h 276 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c701 := derived701 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c136, some c116, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c132, c136, c116] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c917, some c131, some c135, some c127, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c859, c917, c131, c135, c127] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c917 := derived917 a h
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c915, some c272, some c273, some c415, some c916, some c50, some c59, some c278, some c277, some c89, some c73, some c829, some c62, some c918, some c113, some c17, some c131, some c18, some c116, some c137, some c880, some c124, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c859, c914, c915, c272, c273, c415, c916, c50, c59, c278, c277, c89, c73, c829, c62, c918, c113, c17, c131, c18, c116, c137, c880, c124] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c915 := derived915 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c415 := derived415 a h
  have h6 : Entails.eval a c916 := derived916 a h
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c277 := h 276 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c829 := derived829 a h
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c918 := derived918 a h
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c131 := h 130 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c116 := h 115 (by decide)
  have h21 : Entails.eval a c137 := h 136 (by decide)
  have h22 : Entails.eval a c880 := derived880 a h
  have h23 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c915, some c919, some c53, some c107, some c81, some c89, some c16, some c50, some c59, some c278, some c277, some c270, some c260, some c131, some c274, some c917, some c879, some c880, some c124, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c859, c914, c915, c919, c53, c107, c81, c89, c16, c50, c59, c278, c277, c270, c260, c131, c274, c917, c879, c880, c124] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c915 := derived915 a h
  have h3 : Entails.eval a c919 := derived919 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c278 := h 277 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c274 := h 273 (by decide)
  have h17 : Entails.eval a c917 := derived917 a h
  have h18 : Entails.eval a c879 := derived879 a h
  have h19 : Entails.eval a c880 := derived880 a h
  have h20 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c763, some c920, some c485, some c415, some c52, some c71, some c458, some c404, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c914, c859, c763, c920, c485, c415, c52, c71, c458, c404] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c920 := derived920 a h
  have h4 : Entails.eval a c485 := derived485 a h
  have h5 : Entails.eval a c415 := derived415 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c458 := derived458 a h
  have h9 : Entails.eval a c404 := derived404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c914, some c859, some c920, some c921, some c58, some c79, some c81, some c71, some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c763, c914, c859, c920, c921, c58, c79, c81, c71] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c920 := derived920 a h
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨45, by decide⟩, true), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c914, some c859, some c88, some c267, some c64, some c268, some c12, some c18, some c125, some c496, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c922, c914, c859, c88, c267, c64, c268, c12, c18, c125, c496] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c496 := derived496 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c922, some c914, some c859, some c88, some c79, some c265, some c267, some c51, some c557, some c923, some c110, some c119, some c286, some c906, some c109, some c608, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c763, c922, c914, c859, c88, c79, c265, c267, c51, c557, c923, c110, c119, c286, c906, c109, c608] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c859 := derived859 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c557 := derived557 a h
  have h10 : Entails.eval a c923 := derived923 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c906 := derived906 a h
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c608 := derived608 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c922, some c924, some c88, some c79, some c265, some c267, some c268, some c109, some c608, some c328, some c906, some c389, some c391, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c914, c859, c922, c924, c88, c79, c265, c267, c268, c109, c608, c328, c906, c389, c391] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c924 := derived924 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c608 := derived608 a h
  have h11 : Entails.eval a c328 := derived328 a h
  have h12 : Entails.eval a c906 := derived906 a h
  have h13 : Entails.eval a c389 := derived389 a h
  have h14 : Entails.eval a c391 := derived391 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c922, some c136, some c503, some c391, some c143, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c859, c922, c136, c503, c391, c143] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c503 := derived503 a h
  have h4 : Entails.eval a c391 := derived391 a h
  have h5 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c922, some c265, some c53, some c267, some c268, some c71, some c79, some c88, some c924, some c925, some c397, some c73, some c110, some c12, some c125, some c926, some c120, some c135, some c143, some c391, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c914, c859, c922, c265, c53, c267, c268, c71, c79, c88, c924, c925, c397, c73, c110, c12, c125, c926, c120, c135, c143, c391] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c924 := derived924 a h
  have h11 : Entails.eval a c925 := derived925 a h
  have h12 : Entails.eval a c397 := derived397 a h
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c12 := h 11 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c926 := derived926 a h
  have h18 : Entails.eval a c120 := h 119 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  have h20 : Entails.eval a c143 := h 142 (by decide)
  have h21 : Entails.eval a c391 := derived391 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c922, some c763, some c53, some c267, some c51, some c927, some c283, some c282, some c73, some c650, some c278, some c831, some c324, some c82, some c517, some c55, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c859, c914, c922, c763, c53, c267, c51, c927, c283, c282, c73, c650, c278, c831, c324, c82, c517, c55] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c763 := derived763 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c927 := derived927 a h
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c650 := derived650 a h
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c831 := derived831 a h
  have h14 : Entails.eval a c324 := derived324 a h
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c517 := derived517 a h
  have h17 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c18, some c127, some c129, some c140, some c17, some c114, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c859, c914, c18, c127, c129, c140, c17, c114] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨6, by decide⟩, false), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c922, some c914, some c53, some c267, some c928, some c51, some c283, some c73, some c334, some c282, some c268, some c69, some c929, some c120, some c332, some c17, some c123, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c763, c859, c922, c914, c53, c267, c928, c51, c283, c73, c334, c282, c268, c69, c929, c120, c332, c17, c123] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c914 := derived914 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c928 := derived928 a h
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c334 := derived334 a h
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c929 := derived929 a h
  have h15 : Entails.eval a c120 := h 119 (by decide)
  have h16 : Entails.eval a c332 := derived332 a h
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c922, some c763, some c53, some c267, some c928, some c51, some c283, some c73, some c334, some c62, some c930, some c464, some c463, some c26, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c859, c922, c763, c53, c267, c928, c51, c283, c73, c334, c62, c930, c464, c463, c26] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c928 := derived928 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c334 := derived334 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c930 := derived930 a h
  have h12 : Entails.eval a c464 := derived464 a h
  have h13 : Entails.eval a c463 := derived463 a h
  have h14 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c922, some c859, some c914, some c928, some c53, some c267, some c268, some c51, some c283, some c282, some c73, some c334, some c931, some c831, some c278, some c263, some c813, some c918, some c116, some c880, some c141, some c140, some c556, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c763, c922, c859, c914, c928, c53, c267, c268, c51, c283, c282, c73, c334, c931, c831, c278, c263, c813, c918, c116, c880, c141, c140, c556] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c914 := derived914 a h
  have h4 : Entails.eval a c928 := derived928 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c334 := derived334 a h
  have h13 : Entails.eval a c931 := derived931 a h
  have h14 : Entails.eval a c831 := derived831 a h
  have h15 : Entails.eval a c278 := h 277 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c813 := derived813 a h
  have h18 : Entails.eval a c918 := derived918 a h
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c880 := derived880 a h
  have h21 : Entails.eval a c141 := h 140 (by decide)
  have h22 : Entails.eval a c140 := h 139 (by decide)
  have h23 : Entails.eval a c556 := derived556 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c914, some c859, some c53, some c268, some c267, some c928, some c932, some c71, some c106, some c259, some c13, some c114, some c120, some c140, some c721, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c922, c914, c859, c53, c268, c267, c928, c932, c71, c106, c259, c13, c114, c120, c140, c721] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c928 := derived928 a h
  have h7 : Entails.eval a c932 := derived932 a h
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c721 := derived721 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c922, some c859, some c297, some c52, some c106, some c258, some c13, some c267, some c114, some c120, some c259, some c140, some c721, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c914, c922, c859, c297, c52, c106, c258, c13, c267, c114, c120, c259, c140, c721] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c721 := derived721 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c763, some c859, some c51, some c934, some c283, some c933, some c89, some c282, some c630, some c81, some c69, some c278, some c464, some c463, some c26, some c813, some c918, some c116, some c880, some c141, some c140, some c127, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c914, c763, c859, c51, c934, c283, c933, c89, c282, c630, c81, c69, c278, c464, c463, c26, c813, c918, c116, c880, c141, c140, c127] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c934 := derived934 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c933 := derived933 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c630 := derived630 a h
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c464 := derived464 a h
  have h14 : Entails.eval a c463 := derived463 a h
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c813 := derived813 a h
  have h17 : Entails.eval a c918 := derived918 a h
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c880 := derived880 a h
  have h20 : Entails.eval a c141 := h 140 (by decide)
  have h21 : Entails.eval a c140 := h 139 (by decide)
  have h22 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c922, some c859, some c51, some c934, some c283, some c935, some c267, some c269, some c260, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c763, c922, c859, c51, c934, c283, c935, c267, c269, c260] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c934 := derived934 a h
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c935 := derived935 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c914, some c922, some c936, some c265, some c266, some c933, some c89, some c81, some c51, some c283, some c282, some c264, some c69, some c278, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c763, c914, c922, c936, c265, c266, c933, c89, c81, c51, c283, c282, c264, c69, c278] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c933 := derived933 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨55, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c859, some c914, some c936, some c265, some c260, some c267, some c56, some c110, some c937, some c266, some c933, some c89, some c81, some c314, some c312, some c26, some c12, some c125, some c16, some c926, some c120, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c922, c859, c914, c936, c265, c260, c267, c56, c110, c937, c266, c933, c89, c81, c314, c312, c26, c12, c125, c16, c926, c120] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c937 := derived937 a h
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c933 := derived933 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c314 := derived314 a h
  have h15 : Entails.eval a c312 := derived312 a h
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c125 := h 124 (by decide)
  have h19 : Entails.eval a c16 := h 15 (by decide)
  have h20 : Entails.eval a c926 := derived926 a h
  have h21 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c922, some c859, some c937, some c936, some c265, some c266, some c933, some c89, some c260, some c110, some c56, some c267, some c938, some c64, some c18, some c120, some c118, some c496, some c142, some c125, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c914, c922, c859, c937, c936, c265, c266, c933, c89, c260, c110, c56, c267, c938, c64, c18, c120, c118, c496, c142, c125] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c937 := derived937 a h
  have h4 : Entails.eval a c936 := derived936 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c933 := derived933 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c938 := derived938 a h
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c118 := h 117 (by decide)
  have h18 : Entails.eval a c496 := derived496 a h
  have h19 : Entails.eval a c142 := h 141 (by decide)
  have h20 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c859, some c914, some c922, some c51, some c933, some c81, some c89, some c936, some c266, some c265, some c937, some c939, some c286, some c403, some c925, some c107, some c504, some c16, some c54, some c778, some c114, some c391, some c906, some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c763, c859, c914, c922, c51, c933, c81, c89, c936, c266, c265, c937, c939, c286, c403, c925, c107, c504, c16, c54, c778, c114, c391, c906] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c922 := derived922 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c933 := derived933 a h
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c936 := derived936 a h
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c937 := derived937 a h
  have h12 : Entails.eval a c939 := derived939 a h
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c403 := derived403 a h
  have h15 : Entails.eval a c925 := derived925 a h
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c504 := derived504 a h
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c778 := derived778 a h
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c391 := derived391 a h
  have h23 : Entails.eval a c906 := derived906 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c940, some c55, some c492, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c859, c940, c55, c492] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c940 := derived940 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c492 := derived492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c940, some c914, some c859, some c485, some c403, some c88, some c54, some c941, some c267, some c274, some c504, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c922, c940, c914, c859, c485, c403, c88, c54, c941, c267, c274, c504] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c940 := derived940 a h
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c859 := derived859 a h
  have h4 : Entails.eval a c485 := derived485 a h
  have h5 : Entails.eval a c403 := derived403 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c941 := derived941 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c504 := derived504 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c940, some c859, some c267, some c274, some c260, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c922, c940, c859, c267, c274, c260] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c940 := derived940 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c940, some c922, some c942, some c397, some c943, some c485, some c260, some c110, some c56, some c923, some c71, some c81, some c89, some c64, some c900, some c499, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c859, c914, c940, c922, c942, c397, c943, c485, c260, c110, c56, c923, c71, c81, c89, c64, c900, c499] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c922 := derived922 a h
  have h4 : Entails.eval a c942 := derived942 a h
  have h5 : Entails.eval a c397 := derived397 a h
  have h6 : Entails.eval a c943 := derived943 a h
  have h7 : Entails.eval a c485 := derived485 a h
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c923 := derived923 a h
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c900 := derived900 a h
  have h17 : Entails.eval a c499 := derived499 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c914, some c763, some c940, some c922, some c485, some c942, some c397, some c943, some c944, some c265, some c52, some c258, some c79, some c88, some c493, some c497, some c64, some c30, some c900, some c499, some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c859, c914, c763, c940, c922, c485, c942, c397, c943, c944, c265, c52, c258, c79, c88, c493, c497, c64, c30, c900, c499] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c940 := derived940 a h
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c485 := derived485 a h
  have h6 : Entails.eval a c942 := derived942 a h
  have h7 : Entails.eval a c397 := derived397 a h
  have h8 : Entails.eval a c943 := derived943 a h
  have h9 : Entails.eval a c944 := derived944 a h
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c493 := derived493 a h
  have h16 : Entails.eval a c497 := derived497 a h
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c30 := h 29 (by decide)
  have h19 : Entails.eval a c900 := derived900 a h
  have h20 : Entails.eval a c499 := derived499 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c922, some c763, some c940, some c945, some c265, some c287, some c282, some c828, some c79, some c493, some c497, some c836, some c838, some c30, some c149, some c146, some c21, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c914, c922, c763, c940, c945, c265, c287, c282, c828, c79, c493, c497, c836, c838, c30, c149, c146, c21] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c922 := derived922 a h
  have h2 : Entails.eval a c763 := derived763 a h
  have h3 : Entails.eval a c940 := derived940 a h
  have h4 : Entails.eval a c945 := derived945 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c828 := derived828 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c493 := derived493 a h
  have h11 : Entails.eval a c497 := derived497 a h
  have h12 : Entails.eval a c836 := derived836 a h
  have h13 : Entails.eval a c838 := derived838 a h
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c763, some c940, some c81, some c336, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c914, c763, c940, c81, c336] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c336 := derived336 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨45, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c922, some c914, some c940, some c945, some c265, some c54, some c287, some c282, some c946, some c828, some c837, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c922, c914, c940, c945, c265, c54, c287, c282, c946, c828, c837] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c922 := derived922 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c945 := derived945 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c946 := derived946 a h
  have h9 : Entails.eval a c828 := derived828 a h
  have h10 : Entails.eval a c837 := derived837 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c859, some c940, some c763, some c922, some c265, some c943, some c272, some c947, some c493, some c497, some c30, some c948, some c88, some c62, some c499, some c127, some c917, some c18, some c498, some c116, some c138, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c914, c859, c940, c763, c922, c265, c943, c272, c947, c493, c497, c30, c948, c88, c62, c499, c127, c917, c18, c498, c116, c138] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c763 := derived763 a h
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c943 := derived943 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c947 := derived947 a h
  have h9 : Entails.eval a c493 := derived493 a h
  have h10 : Entails.eval a c497 := derived497 a h
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c948 := derived948 a h
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c499 := derived499 a h
  have h16 : Entails.eval a c127 := h 126 (by decide)
  have h17 : Entails.eval a c917 := derived917 a h
  have h18 : Entails.eval a c18 := h 17 (by decide)
  have h19 : Entails.eval a c498 := derived498 a h
  have h20 : Entails.eval a c116 := h 115 (by decide)
  have h21 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c763, some c945, some c89, some c81, some c68, some c69, some c282, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c914, c763, c945, c89, c81, c68, c69, c282] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c945 := derived945 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c859, some c945, some c914, some c763, some c922, some c940, some c943, some c265, some c949, some c53, some c107, some c81, some c89, some c16, some c493, some c497, some c30, some c950, some c278, some c837, some c918, some c813, some c131, some c498, some c884, some c141, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c859, c945, c914, c763, c922, c940, c943, c265, c949, c53, c107, c81, c89, c16, c493, c497, c30, c950, c278, c837, c918, c813, c131, c498, c884, c141] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c859 := derived859 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c763 := derived763 a h
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c940 := derived940 a h
  have h6 : Entails.eval a c943 := derived943 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c949 := derived949 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c493 := derived493 a h
  have h15 : Entails.eval a c497 := derived497 a h
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c950 := derived950 a h
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c837 := derived837 a h
  have h20 : Entails.eval a c918 := derived918 a h
  have h21 : Entails.eval a c813 := derived813 a h
  have h22 : Entails.eval a c131 := h 130 (by decide)
  have h23 : Entails.eval a c498 := derived498 a h
  have h24 : Entails.eval a c884 := derived884 a h
  have h25 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c945, some c940, some c922, some c859, some c260, some c268, some c272, some c264, some c419, some c521, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c945, c940, c922, c859, c260, c268, c272, c264, c419, c521] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c945 := derived945 a h
  have h1 : Entails.eval a c940 := derived940 a h
  have h2 : Entails.eval a c922 := derived922 a h
  have h3 : Entails.eval a c859 := derived859 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c419 := derived419 a h
  have h9 : Entails.eval a c521 := derived521 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c951, some c952, some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c951, c952] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c951 := derived951 a h
  have h1 : Entails.eval a c952 := derived952 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c953, some c945, some c283, some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c953, c945, c283] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c953 := derived953 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c953, some c945, some c277, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c953, c945, c277] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c953 := derived953 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c954, some c945, some c521, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c954, c945, c521] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c954 := derived954 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c521 := derived521 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c955, some c763, some c954, some c68, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c955, c763, c954, c68] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c763 := derived763 a h
  have h2 : Entails.eval a c954 := derived954 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c955, some c950, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c955, c950] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c950 := derived950 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c956, some c955, some c954, some c914, some c922, some c828, some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c956, c955, c954, c914, c922, c828] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c956 := derived956 a h
  have h1 : Entails.eval a c955 := derived955 a h
  have h2 : Entails.eval a c954 := derived954 a h
  have h3 : Entails.eval a c914 := derived914 a h
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c828 := derived828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c957, some c914, some c79, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c957, c914, c79] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c957 := derived957 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c859, some c53, some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c958, c859, c53] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c859 := derived859 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c959, some c940, some c960, some c961, some c829]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c958, c959, c940, c960, c961, c829] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c959 := derived959 a h
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c960 := derived960 a h
  have h4 : Entails.eval a c961 := derived961 a h
  have h5 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived962

end CochromaticTwenty.Certificates.B16_8_1
