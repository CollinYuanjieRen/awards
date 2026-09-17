import MerLeanExperiment.Certificates.B16_6_1.Steps0400_0499

/-! Generated from the actual pinned b16_6_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c874 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c863, some c169, some c166, some c175, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c865, c863, c169, c166, c175] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c223, some c228, some c213, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c223, c228, c213] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c223 := h 222 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c865, some c276, some c352, some c874, some c116, some c875, some c136, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c864, c865, c276, c352, c874, c116, c875, c136] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c874 := derived874 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c875 := derived875 a h
  have h7 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c863, some c864, some c865, some c868, some c674, some c94, some c871, some c869, some c876, some c873, some c297, some c673, some c223, some c228, some c875, some c215, some c263, some c111, some c193, some c154, some c245, some c121, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c746, c863, c864, c865, c868, c674, c94, c871, c869, c876, c873, c297, c673, c223, c228, c875, c215, c263, c111, c193, c154, c245, c121] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c864 := derived864 a h
  have h3 : Entails.eval a c865 := derived865 a h
  have h4 : Entails.eval a c868 := derived868 a h
  have h5 : Entails.eval a c674 := derived674 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c869 := derived869 a h
  have h9 : Entails.eval a c876 := derived876 a h
  have h10 : Entails.eval a c873 := derived873 a h
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c673 := derived673 a h
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c875 := derived875 a h
  have h16 : Entails.eval a c215 := h 214 (by decide)
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c111 := h 110 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c154 := h 153 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c746, some c864, some c868, some c869, some c674, some c94, some c871, some c876, some c673, some c873, some c297, some c298, some c877, some c220, some c206, some c198, some c314, some c320, some c244, some c302, some c217, some c350, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c863, c746, c864, c868, c869, c674, c94, c871, c876, c673, c873, c297, c298, c877, c220, c206, c198, c314, c320, c244, c302, c217, c350] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c864 := derived864 a h
  have h3 : Entails.eval a c868 := derived868 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c674 := derived674 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c876 := derived876 a h
  have h9 : Entails.eval a c673 := derived673 a h
  have h10 : Entails.eval a c873 := derived873 a h
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c877 := derived877 a h
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c320 := h 319 (by decide)
  have h19 : Entails.eval a c244 := h 243 (by decide)
  have h20 : Entails.eval a c302 := h 301 (by decide)
  have h21 : Entails.eval a c217 := h 216 (by decide)
  have h22 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c863, some c865, some c864, some c869, some c661, some c368, some c371, some c92, some c673, some c100, some c109, some c276, some c716, some c670, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c746, c863, c865, c864, c869, c661, c368, c371, c92, c673, c100, c109, c276, c716, c670] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c864 := derived864 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c661 := derived661 a h
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c673 := derived673 a h
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c716 := derived716 a h
  have h14 : Entails.eval a c670 := derived670 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c865, some c879, some c674, some c673, some c276, some c874, some c136, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c864, c865, c879, c674, c673, c276, c874, c136] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c879 := derived879 a h
  have h3 : Entails.eval a c674 := derived674 a h
  have h4 : Entails.eval a c673 := derived673 a h
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c874 := derived874 a h
  have h7 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c865, some c863, some c746, some c868, some c880, some c879, some c878, some c871, some c674, some c869, some c661, some c276, some c352, some c874, some c71, some c116, some c100, some c228, some c92, some c64, some c202, some c317, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c864, c865, c863, c746, c868, c880, c879, c878, c871, c674, c869, c661, c276, c352, c874, c71, c116, c100, c228, c92, c64, c202, c317] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c746 := derived746 a h
  have h4 : Entails.eval a c868 := derived868 a h
  have h5 : Entails.eval a c880 := derived880 a h
  have h6 : Entails.eval a c879 := derived879 a h
  have h7 : Entails.eval a c878 := derived878 a h
  have h8 : Entails.eval a c871 := derived871 a h
  have h9 : Entails.eval a c674 := derived674 a h
  have h10 : Entails.eval a c869 := derived869 a h
  have h11 : Entails.eval a c661 := derived661 a h
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c874 := derived874 a h
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c116 := h 115 (by decide)
  have h17 : Entails.eval a c100 := h 99 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c92 := h 91 (by decide)
  have h20 : Entails.eval a c64 := h 63 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c864, some c71, some c35, some c263, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c865, c864, c71, c35, c263] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c864 := derived864 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c746, some c868, some c661, some c869, some c879, some c674, some c94, some c871, some c878, some c881, some c882, some c100, some c103, some c92, some c64, some c83, some c317, some c350, some c302, some c304, some c331, some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c863, c746, c868, c661, c869, c879, c674, c94, c871, c878, c881, c882, c100, c103, c92, c64, c83, c317, c350, c302, c304, c331] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c868 := derived868 a h
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c869 := derived869 a h
  have h5 : Entails.eval a c879 := derived879 a h
  have h6 : Entails.eval a c674 := derived674 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c871 := derived871 a h
  have h9 : Entails.eval a c878 := derived878 a h
  have h10 : Entails.eval a c881 := derived881 a h
  have h11 : Entails.eval a c882 := derived882 a h
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c350 := h 349 (by decide)
  have h19 : Entails.eval a c302 := h 301 (by decide)
  have h20 : Entails.eval a c304 := h 303 (by decide)
  have h21 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c865, some c671, some c287, some c277, some c367, some c869, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c864, c865, c671, c287, c277, c367, c869] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c671 := derived671 a h
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c869 := derived869 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨30, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c350, some c273, some c47, some c103, some c108, some c79, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c356, c350, c273, c47, c103, c108, c79] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c103, some c108, some c882, some c312, some c53, some c61, some c353, some c317, some c869, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c865, c103, c108, c882, c312, c53, c61, c353, c317, c869] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c882 := derived882 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c869 := derived869 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨30, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c746, some c865, some c864, some c883, some c92, some c94, some c884, some c885, some c55, some c886, some c83, some c49, some c358, some c874, some c145, some c748, some c277, some c259, some c869, some c304, some c317, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c863, c746, c865, c864, c883, c92, c94, c884, c885, c55, c886, c83, c49, c358, c874, c145, c748, c277, c259, c869, c304, c317] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c865 := derived865 a h
  have h3 : Entails.eval a c864 := derived864 a h
  have h4 : Entails.eval a c883 := derived883 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c884 := derived884 a h
  have h8 : Entails.eval a c885 := derived885 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c886 := derived886 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c874 := derived874 a h
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c748 := derived748 a h
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c259 := h 258 (by decide)
  have h19 : Entails.eval a c869 := derived869 a h
  have h20 : Entails.eval a c304 := h 303 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c865, some c864, some c257, some c301, some c297, some c275, some c205, some c660, some c669, some c670, some c57, some c33, some c200, some c194, some c228, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c883, c865, c864, c257, c301, c297, c275, c205, c660, c669, c670, c57, c33, c200, c194, c228] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c864 := derived864 a h
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c297 := h 296 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c660 := derived660 a h
  have h9 : Entails.eval a c669 := derived669 a h
  have h10 : Entails.eval a c670 := derived670 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c863, some c94, some c99, some c660, some c665, some c671, some c109, some c13, some c39, some c44, some c367, some c290, some c133, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c746, c863, c94, c99, c660, c665, c671, c109, c13, c39, c44, c367, c290, c133] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c660 := derived660 a h
  have h5 : Entails.eval a c665 := derived665 a h
  have h6 : Entails.eval a c671 := derived671 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c865, some c864, some c277, some c716, some c661, some c109, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c865, c864, c277, c716, c661, c109] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c865 := derived865 a h
  have h1 : Entails.eval a c864 := derived864 a h
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c661 := derived661 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c864, some c865, some c72, some c36, some c268, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c864, c865, c72, c36, c268] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c864 := derived864 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c863, some c94, some c99, some c105, some c890, some c889, some c891, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c746, c863, c94, c99, c105, c890, c889, c891] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c889 := derived889 a h
  have h7 : Entails.eval a c891 := derived891 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c863, some c864, some c865, some c94, some c888, some c892, some c92, some c887, some c884, some c674, some c277, some c361, some c347, some c367, some c891, some c669, some c108, some c296, some c47, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c746, c863, c864, c865, c94, c888, c892, c92, c887, c884, c674, c277, c361, c347, c367, c891, c669, c108, c296, c47] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c864 := derived864 a h
  have h3 : Entails.eval a c865 := derived865 a h
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c888 := derived888 a h
  have h6 : Entails.eval a c892 := derived892 a h
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c887 := derived887 a h
  have h9 : Entails.eval a c884 := derived884 a h
  have h10 : Entails.eval a c674 := derived674 a h
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c361 := h 360 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c891 := derived891 a h
  have h16 : Entails.eval a c669 := derived669 a h
  have h17 : Entails.eval a c108 := h 107 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c746, some c883, some c865, some c864, some c94, some c893, some c258, some c276, some c292, some c298, some c58, some c103, some c108, some c43, some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c863, c746, c883, c865, c864, c94, c893, c258, c276, c292, c298, c58, c103, c108, c43] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c865 := derived865 a h
  have h4 : Entails.eval a c864 := derived864 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c893 := derived893 a h
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c894, some c879, some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c894, c879] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c894 := derived894 a h
  have h1 : Entails.eval a c879 := derived879 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c895, some c865, some c353, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c895, c865, c353] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c895, some c866, some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c895, c866] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c895 := derived895 a h
  have h1 : Entails.eval a c866 := derived866 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c897, some c894, some c362, some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c897, c894, c362] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c897 := derived897 a h
  have h1 : Entails.eval a c894 := derived894 a h
  have h2 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c897, some c894, some c368, some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c897, c894, c368] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c897 := derived897 a h
  have h1 : Entails.eval a c894 := derived894 a h
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c865, some c864, some c899, some c835, some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c898, c865, c864, c899, c835] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c865 := derived865 a h
  have h2 : Entails.eval a c864 := derived864 a h
  have h3 : Entails.eval a c899 := derived899 a h
  have h4 : Entails.eval a c835 := derived835 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c900, some c896, some c899, some c340]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c898, c900, c896, c899, c340] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c900 := derived900 a h
  have h2 : Entails.eval a c896 := derived896 a h
  have h3 : Entails.eval a c899 := derived899 a h
  have h4 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived901

end CochromaticTwenty.Certificates.B16_6_1
